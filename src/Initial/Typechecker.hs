{-# LANGUAGE NamedFieldPuns #-}

module Initial.Typechecker where

import Data.Map as Map hiding (foldl, map)
import Data.List as List
import Data.Either
import Text.Printf (printf)
import Control.Monad
import Control.Monad.Except
import Initial.AST

-- Errors
data TCError =
    UnknownClassError Name
  | UnknownFieldError Name
  | UnknownMethodError Name
  | UnboundVariableError Name
  | TypeMismatchError Type Type
  | ImmutableFieldError Expr
  | NonLValError Expr
  | PrimitiveNullError Type
  | NonClassTypeError Type
  | NonArrowTypeError Type
  | UninferrableError Expr

instance Show TCError where
  show (UnknownClassError c)  = printf "Unknown class '%s'"  c
  show (UnknownFieldError f)  = printf "Unknown field '%s'"  f
  show (UnknownMethodError m) = printf "Unknown method '%s'" m
  show (UnboundVariableError x) = printf "Unbound variable '%s'" x
  show (TypeMismatchError actual expected) =
    printf "Type '%s' does not match expected type '%s'"
           (show actual) (show expected)
  show (ImmutableFieldError e) =
    printf "Cannot write to immutable field '%s'" (show e)
  show (NonLValError e) =
    printf "Cannot assign to expression '%s'" (show e)
  show (PrimitiveNullError t) =
    printf "Type '%s' cannot be null" (show t)
  show (NonClassTypeError t) =
    printf "Expected class type, got '%s'" (show t)
  show (NonArrowTypeError t) =
    printf "Expected function type, got '%s'" (show t)
  show (UninferrableError e) =
    printf "Cannot infer the type of '%s'" (show e)

-- Environment
data Env =
  Env {ctable :: Map Name ClassDef
      ,vartable :: Map Name Type }

emptyEnv :: Env
emptyEnv = Env {ctable = Map.empty
               ,vartable = Map.empty}

lookupClass :: Env -> Name -> Except TCError ClassDef
lookupClass Env{ctable} c =
  case Map.lookup c ctable of
    Just cdef -> return cdef
    Nothing -> throwError $ UnknownClassError c

lookupField :: Env -> Type -> Name -> Except TCError FieldDef
lookupField env (ClassType c) f = do
  ClassDef{fields} <- lookupClass env c
  case List.find ((== f) . fname) fields of
    Just fdef -> return fdef
    Nothing -> throwError $ UnknownFieldError f
lookupField _ ty _ = throwError $ NonClassTypeError ty

lookupMethod :: Env -> Type -> Name -> Except TCError MethodDef
lookupMethod env (ClassType c) m = do
  ClassDef{methods} <- lookupClass env c
  case List.find ((== m) . mname) methods of
    Just mdef -> return mdef
    Nothing -> throwError $ UnknownMethodError m
lookupMethod _ ty _ = throwError $ NonClassTypeError ty

lookupVar :: Env -> Name -> Except TCError Type
lookupVar Env{vartable} x =
  case Map.lookup x vartable of
    Just t -> return t
    Nothing -> throwError $ UnboundVariableError x

genEnv :: Program -> Env
genEnv (Program classes) = foldl generateEnv emptyEnv classes
  where
    generateEnv :: Env -> ClassDef -> Env
    generateEnv env cls = Env {ctable = Map.insert (cname cls) cls (ctable env)
                              ,vartable = vartable env}

addVariable :: Env -> Name -> Type -> Env
addVariable env@Env{vartable} x t =
  env{vartable = Map.insert x t vartable}

addParameters :: Env -> [Param] -> Env
addParameters = foldl addParameter
  where
    addParameter env (Param name ty) = addVariable env name ty

tcProgram :: Program -> Either TCError Program
tcProgram p = do
  let env = genEnv p
  runExcept $ typecheck env p

class Typecheckable a where
  typecheck :: Env -> a -> Except TCError a

-- Type checking the well-formedness of types
instance Typecheckable Type where
  typecheck env (ClassType c) = do
    _ <- lookupClass env c
    return $ ClassType c
  typecheck _ IntType = return IntType
  typecheck _ UnitType = return UnitType
  typecheck _ BoolType = return BoolType
  typecheck env (Arrow ts t) = do
    ts' <- mapM (typecheck env) (t:ts)
    return $ Arrow (tail ts') (head ts')

instance Typecheckable Program where
  typecheck env (Program cls) = Program <$> mapM (typecheck env) cls

instance Typecheckable ClassDef where
  typecheck env cdef@ClassDef{cname, fields, methods} = do
    let env' = addVariable env thisName (ClassType cname)
    fields' <- mapM (typecheck env') fields
    methods' <- mapM (typecheck env') methods
    return $ cdef {fields = fields'
                  ,methods = methods'}

instance Typecheckable FieldDef where
  typecheck env fdef@FieldDef{ftype} = do
    ftype' <- typecheck env ftype
    return fdef{ftype = ftype'}

instance Typecheckable Param where
  typecheck env param@(Param {ptype}) = do
    ptype' <- typecheck env ptype
    return param{ptype = ptype'}

instance Typecheckable MethodDef where
  typecheck env mdef@(MethodDef {mparams, mbody, mtype}) = do
    -- typecheck the well-formedness of types of method parameters
    mparams' <- mapM (typecheck env) mparams
    mtype' <- typecheck env mtype

    -- extend environment with method parameters and typecheck body
    let env' = addParameters env mparams
    mbody' <- hasType env' mbody mtype'

    return $ mdef {mparams = mparams'
                  ,mtype = mtype'
                  ,mbody = mbody'}

instance Typecheckable Expr where
  typecheck env e@(BoolLit {}) = return $ setType BoolType e

  typecheck env e@(IntLit {}) = return $ setType IntType e

  typecheck env e@(Lambda {params, body}) = do
    params' <- mapM (typecheck env) params
    let env' = addParameters env params'
    body' <- typecheck env' body
    let parameterTypes = map ptype params'
        bodyType = getType body'
        funType = Arrow parameterTypes bodyType
    return $ setType funType e{params = params'
                              ,body = body'}

  typecheck env e@(VarAccess {name}) = do
    ty <- lookupVar env name
    return $ setType ty e

  typecheck env e@(FieldAccess {target, name}) = do
    target' <- typecheck env target
    let targetType = getType target'
    FieldDef {ftype} <- lookupField env targetType name
    return $ setType ftype e{target = target'}

  typecheck env e@(Assignment {lhs, rhs}) = do
    unless (isLVal lhs) $
      throwError $ NonLValError lhs

    lhs' <- typecheck env lhs
    let lType = getType lhs'

    rhs' <- hasType env rhs lType
    let rType = getType rhs'

    checkMutability lhs'

    return $ setType UnitType e{lhs = lhs'
                               ,rhs = rhs'}
    where
      checkMutability e@FieldAccess{target, name} = do
        field <- lookupField env (getType target) name
        unless (isVarField field) $
          throwError $ ImmutableFieldError e
      checkMutability _ = return ()

  typecheck env e@(MethodCall {target, name, args}) = do
    target' <- typecheck env target
    let targetType = getType target'
    MethodDef {mparams, mtype} <- lookupMethod env targetType name
    let paramTypes = map ptype mparams
    args' <- zipWithM (hasType env) args paramTypes
    return $ setType mtype $ e{target = target'
                              ,args = args'}

  typecheck env e@(FunctionCall {target, args}) = do
    target' <- typecheck env target
    let targetType = getType target'
    unless (isArrowType targetType) $
      throwError $ NonArrowTypeError targetType
    let paramTypes = tparams targetType
        resultType = tresult targetType
    args' <- zipWithM (hasType env) args paramTypes

    return $ setType resultType e{target = target'
                                 ,args = args'}

  typecheck env e@(BinOp {op, lhs, rhs}) = do
    lhs' <- hasType env lhs IntType
    rhs' <- hasType env rhs IntType
    return $ setType IntType e{lhs = lhs'
                              ,rhs = rhs'}

  typecheck env e@(Cast {body, ty}) = do
    ty' <- typecheck env ty
    body' <- hasType env body ty'
    return $ setType ty' e{body = body'
                          ,ty = ty'}

  typecheck env e@(If {cond, thn, els}) = do
    cond' <- hasType env cond BoolType
    thn' <- typecheck env thn
    let thnType = getType thn'
    els' <- hasType env els thnType
    return $ setType thnType e{cond = cond'
                              ,thn = thn'
                              ,els = els'}

  typecheck env e@(Let {name, val, body}) = do
    val' <- typecheck env val
    let ty = getType val'
        env' = addVariable env name ty
    body' <- typecheck env' body
    let bodyType = getType body'
    return $ setType bodyType e{val = val'
                               ,body = body'}

  typecheck _ e =
    throwError $ UninferrableError e

hasType :: Env -> Expr -> Type -> Except TCError Expr
hasType env e@Null{} expected = do
  unless (isClassType expected) $
    throwError $ PrimitiveNullError expected
  return $ setType expected e
hasType env e expected = do
  e' <- typecheck env e
  let eType = getType e'
  unless (eType == expected) $
    throwError $ TypeMismatchError eType expected
  return $ setType expected e'


-- Test
--testClass1 :: ClassDef
testClass1 =
  ClassDef {cname = "C"
           ,fields = [FieldDef {fmod = Val, fname = "f", ftype = ClassType "Foo"}]
           ,methods = []}

--testClass2 :: ClassDef
testClass2 =
  ClassDef {cname = "D"
           ,fields = [FieldDef {fmod = Val, fname = "g", ftype = ClassType "Bar"}]
           ,methods = [MethodDef {mname = "m", mparams = [], mtype = IntType, mbody = VarAccess Nothing "x"}]}

--testClass2 :: ClassDef
testClass3 =
  [ClassDef {cname = "D"
           ,fields = [FieldDef {fmod = Val, fname = "g", ftype = ClassType "D"}]
           ,methods = [MethodDef {mname = "m", mparams = [], mtype = IntType, mbody = VarAccess Nothing "x"}]},
   ClassDef {cname = "D"
           ,fields = [FieldDef {fmod = Val, fname = "g", ftype = ClassType "D"}]
           ,methods = [MethodDef {mname = "m", mparams = [], mtype = IntType, mbody = VarAccess Nothing "x"}]}]


--testProgram :: Program 'Parsed 'Parsed
testProgram = Program [testClass1, testClass2]
testValidProgram = Program testClass3


testSuite = do
  putStrLn $ "\n************************************************"
  putStrLn $ "1. Initial Version.\n" ++
             "Showing a program with 3 errors:\n" ++
             "- type checker only catches one error\n" ++
             "- there is not support for backtrace\n"
  putStrLn "Output:"
  putStrLn ""
  putStrLn $ show $ fromLeft undefined (tcProgram testProgram)
  putStrLn ""
  putStrLn $ "************************************************"
