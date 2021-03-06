{-# LANGUAGE NamedFieldPuns, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, RankNTypes #-}
module Reader.Typechecker where

import Data.Map as Map hiding (foldl, map)
import Data.List as List
import Data.Maybe (fromJust)
import Data.Either (fromLeft)
import Text.Printf (printf)
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except
import Reader.AST

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

lookupClass :: Name -> Env -> Maybe ClassDef
lookupClass c Env{ctable} = Map.lookup c ctable

lookupVar :: Name -> Env -> Maybe Type
lookupVar x Env{vartable} = Map.lookup x vartable

-- Lookup functions with error messages
findClass :: Type -> TypecheckM ClassDef
findClass ty@(ClassType c) = do
  cls <- asks $ lookupClass c
  case cls of
    Just cdef -> return cdef
    Nothing -> throwError $ UnknownClassError c
findClass ty = throwError $ NonClassTypeError ty

findMethod :: Type -> Name -> TypecheckM MethodDef
findMethod ty m = do
  ClassDef{methods} <- findClass ty
  case List.find ((== m) . mname) methods of
    Just mdef -> return mdef
    Nothing -> throwError $ UnknownMethodError m

findField :: Type -> Name -> TypecheckM FieldDef
findField ty f = do
  ClassDef{fields} <- findClass ty
  case List.find ((== f) . fname) fields of
    Just fdef -> return fdef
    Nothing -> throwError $ UnknownFieldError f

findVar :: Name -> TypecheckM Type
findVar x = do
  result <- asks $ lookupVar x
  case result of
    Just t -> return t
    Nothing -> throwError $ UnboundVariableError x

genEnv :: Program -> Env
genEnv (Program cls) = foldl generateEnv emptyEnv cls
  where
    generateEnv :: Env -> ClassDef -> Env
    generateEnv env cls = Env {ctable = Map.insert (cname cls) cls (ctable env)
                              ,vartable = vartable env}

addVariable :: Name -> Type -> Env -> Env
addVariable x t env@Env{vartable} =
  env{vartable = Map.insert x t vartable}

addParameters :: [Param] -> Env -> Env
addParameters params env = foldl addParameter env params
  where
    addParameter env (Param name ty) = addVariable name ty env

type TypecheckM a = forall m. (MonadReader Env m, MonadError TCError m) => m a

tcProgram :: Program -> Either TCError Program
tcProgram p = do
  let env = genEnv p
      exceptM = runReaderT (typecheck p) env
  runExcept exceptM

class Typecheckable a where
  typecheck :: a -> TypecheckM a

-- Type checking the well-formedness of types
instance Typecheckable Type where
  typecheck (ClassType c) = do
    _ <- findClass (ClassType c)
    return $ ClassType c
  typecheck IntType = return IntType
  typecheck BoolType = return BoolType
  typecheck UnitType = return UnitType
  typecheck (Arrow ts t) = do
    ts' <- mapM typecheck ts
    t' <- typecheck t
    return $ Arrow ts' t'

instance Typecheckable Program where
  typecheck (Program cls) = Program <$> mapM typecheck cls

instance Typecheckable ClassDef where
  typecheck cdef@ClassDef{cname, fields, methods} = do
    let withThisAdded = local $ addVariable thisName (ClassType cname)
    fields' <- withThisAdded $ mapM typecheck fields
    methods' <- withThisAdded $ mapM typecheck methods
    return $ cdef {fields = fields'
                  ,methods = methods'}

instance Typecheckable FieldDef where
  typecheck fdef@FieldDef{ftype} = do
    ftype' <- typecheck ftype
    return fdef{ftype = ftype'}

instance Typecheckable Param where
  typecheck param@(Param {ptype}) = do
    ptype' <- typecheck ptype
    return param{ptype = ptype'}

instance Typecheckable MethodDef where
  typecheck mdef@(MethodDef {mparams, mbody, mtype}) = do
    -- typecheck the well-formedness of types of method parameters
    mparams' <- mapM typecheck mparams
    mtype' <- typecheck mtype

    -- extend environment with method parameters and typecheck body
    mbody' <- local (addParameters mparams) $ hasType mbody mtype'

    return $ mdef {mparams = mparams'
                  ,mtype = mtype'
                  ,mbody = mbody'}

instance Typecheckable Expr where
  typecheck e@(BoolLit {}) = return $ setType BoolType e

  typecheck e@(IntLit {}) = return $ setType IntType e

  typecheck e@(Lambda {params, body}) = do
    params' <- mapM typecheck params
    body' <- local (addParameters params) $ typecheck body
    let parameterTypes = map ptype params'
        bodyType = getType body'
        funType = Arrow parameterTypes bodyType
    return $ setType funType e{params = params'
                              ,body = body'}

  typecheck e@(VarAccess {name}) = do
    ty <- findVar name
    return $ setType ty e

  typecheck e@(FieldAccess {target, name}) = do
    target' <- typecheck target
    let targetType = getType target'

    FieldDef {ftype} <- findField targetType name
    return $ setType ftype e{target = target'}

  typecheck e@(Assignment {lhs, rhs}) = do
    unless (isLVal lhs) $
      throwError $ NonLValError lhs

    lhs' <- typecheck lhs
    let lType = getType lhs'

    rhs' <- hasType rhs lType
    let rType = getType rhs'

    checkMutability lhs'

    return $ setType UnitType e{lhs = lhs'
                               ,rhs = rhs'}
    where
      checkMutability e@FieldAccess{target, name} = do
        field <- findField (getType e) name
        unless (isVarField field) $
          throwError $ ImmutableFieldError e
      checkMutability _ = return ()

  typecheck e@(MethodCall {target, name, args}) = do
    target' <- typecheck target
    let targetType = getType target'
    MethodDef {mparams, mtype} <- findMethod targetType name
    let paramTypes = map ptype mparams
    args' <- zipWithM hasType args paramTypes
    return $ setType mtype $ e{target = target'
                              ,args = args'}

  typecheck e@(FunctionCall {target, args}) = do
    target' <- typecheck target
    let targetType = getType target'
    unless (isArrowType targetType) $
      throwError $ NonArrowTypeError targetType
    let paramTypes = tparams targetType
        resultType = tresult targetType
    args' <- zipWithM hasType args paramTypes

    return $ setType resultType e{target = target'
                                 ,args = args'}

  typecheck e@(BinOp {op, lhs, rhs}) = do
    lhs' <- hasType lhs IntType
    rhs' <- hasType rhs IntType
    return $ setType IntType e{lhs = lhs'
                              ,rhs = rhs'}

  typecheck e@(Cast {body, ty}) = do
    ty' <- typecheck ty
    body' <- hasType body ty'
    return $ setType ty' e{body = body'
                          ,ty = ty'}

  typecheck e@(If {cond, thn, els}) = do
    cond' <- hasType cond BoolType
    thn' <- typecheck thn
    let thnType = getType thn'
    els' <- hasType els thnType
    return $ setType thnType e{cond = cond'
                              ,thn = thn'
                              ,els = els'}

  typecheck e@(Let {name, val, body}) = do
    val' <- typecheck val
    let ty = getType val'
    body' <- local (addVariable name ty) $ typecheck body
    let bodyType = getType body'
    return $ setType bodyType e{val = val'
                               ,body = body'}

  typecheck e =
    throwError $ UninferrableError e

hasType :: Expr -> Type -> TypecheckM Expr
hasType e@Null{} expected = do
  unless (isClassType expected) $
    throwError $ PrimitiveNullError expected
  return $ setType expected e
hasType e expected = do
  e' <- typecheck e
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
  putStrLn $ "2. Refactoring to use the Reader monad -- no extensions.\n" ++
             "Showing a program with 3 errors:\n" ++
             "- type checker only catches one error\n" ++
             "- there is not support for backtrace\n"
  putStrLn "Output:"
  putStrLn ""
  putStrLn $ show $ fromLeft undefined (tcProgram testProgram)
  putStrLn ""
  putStrLn $ "************************************************"
