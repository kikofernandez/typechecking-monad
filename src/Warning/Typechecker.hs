{-# LANGUAGE NamedFieldPuns, TypeSynonymInstances, FlexibleInstances,
FlexibleContexts, RankNTypes, ConstrainedClassMethods #-}
module Warning.Typechecker where

import Data.Map as Map hiding (foldl, map)
import Data.List as List
import Data.Maybe(isJust)
import Data.Either (fromRight,fromLeft)
import Text.Printf (printf)
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Writer
import Control.Applicative (liftA2)
import Warning.AST

type TypecheckM a = forall m. (MonadReader Env m,
                               MonadError TCError m,
                               MonadWriter [TCWarning] m) => m a

-- Errors
data TCError = TCError Error Backtrace
data Error =
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

data TCWarning = TCWarning Warning Backtrace
data Warning =
    ShadowedVarWarning Name
  | UnusedVariableWarning Name

tcError :: Error -> TypecheckM a
tcError err = do
  bt <- asks bt
  throwError $ TCError err bt

tcWarning :: Warning -> TypecheckM ()
tcWarning wrn = do
  bt <- asks bt
  tell $ [TCWarning wrn bt]

instance Show TCError where
  show (TCError err bt) =
    " *** Error during typechecking *** \n" ++
    show err ++ "\n" ++ show bt

instance Show TCWarning where
  show (TCWarning wrn bt) =
    " *** Warning during typechecking *** \n" ++
    show wrn ++ "\n" ++ show bt

instance Show Warning where
  show (ShadowedVarWarning x) =
    printf "Variable '%s' shadows previous definition" x
  show (UnusedVariableWarning x) =
    printf "Variable '%s' is never used" x

instance Show Error where
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
      ,vartable :: Map Name Type
      ,bt :: Backtrace}

emptyEnv :: Env
emptyEnv = Env {ctable = Map.empty
               ,vartable = Map.empty
               ,bt = emptyBt}

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
    Nothing -> tcError $ UnknownClassError c
findClass ty = tcError $ NonClassTypeError ty

findMethod :: Type -> Name -> TypecheckM MethodDef
findMethod ty m = do
  ClassDef{methods} <- findClass ty
  case List.find ((== m) . mname) methods of
    Just mdef -> return mdef
    Nothing -> tcError $ UnknownMethodError m

findField :: Type -> Name -> TypecheckM FieldDef
findField ty f = do
  ClassDef{fields} <- findClass ty
  case List.find ((== f) . fname) fields of
    Just fdef -> return fdef
    Nothing -> tcError $ UnknownFieldError f

findVar :: Name -> TypecheckM Type
findVar x = do
  result <- asks $ lookupVar x
  case result of
    Just t -> return t
    Nothing -> tcError $ UnboundVariableError x

isBound :: Name -> TypecheckM Bool
isBound = liftM isJust . asks . lookupVar

genEnv :: Program -> Env
genEnv (Program cls) = foldl generateEnv emptyEnv cls
  where
    generateEnv :: Env -> ClassDef -> Env
    generateEnv env cls = Env {ctable = Map.insert (cname cls) cls (ctable env)
                              ,vartable = vartable env
                              ,bt = emptyBt}

addVariable :: Name -> Type -> Env -> Env
addVariable x t env@Env{vartable} =
  env{vartable = Map.insert x t vartable}

addParameters :: [Param] -> Env -> Env
addParameters params env = foldl addParameter env params
  where
    addParameter env (Param name ty) = addVariable name ty env

tcProgram :: Program -> Either TCError (Program, [TCWarning])
tcProgram p = do
  let env = genEnv p
  runExcept $ runReaderT (runWriterT (doTypecheck p)) env

class Typecheckable a where
  doTypecheck :: a -> TypecheckM a

  typecheck :: (Backtraceable a) => a -> TypecheckM a
  typecheck x = local pushBT $ doTypecheck x
    where
      pushBT env@Env{bt} = env{bt = push x bt}

-- Type checking the well-formedness of types
instance Typecheckable Type where
  doTypecheck (ClassType c) = do
    _ <- findClass (ClassType c)
    return $ ClassType c
  doTypecheck IntType = return IntType
  doTypecheck BoolType = return BoolType
  doTypecheck UnitType = return UnitType
  doTypecheck (Arrow ts t) = do
    ts' <- mapM typecheck ts
    t' <- typecheck t
    return $ Arrow ts' t'

instance Typecheckable Program where
  doTypecheck (Program cls) = Program <$> mapM typecheck cls

instance Typecheckable ClassDef where
  doTypecheck cdef@ClassDef{cname, fields, methods} = do
    let withThisAdded = local $ addVariable thisName (ClassType cname)
    fields' <- withThisAdded $ mapM typecheck fields
    methods' <- withThisAdded $ mapM typecheck methods
    return $ cdef {fields = fields'
                  ,methods = methods'}

instance Typecheckable FieldDef where
  doTypecheck fdef@FieldDef{ftype} = do
    ftype' <- typecheck ftype
    return fdef{ftype = ftype'}

instance Typecheckable Param where
  doTypecheck param@(Param {ptype}) = do
    ptype' <- typecheck ptype
    return param{ptype = ptype'}

instance Typecheckable MethodDef where
  doTypecheck mdef@(MethodDef {mparams, mbody, mtype}) = do
    -- typecheck the well-formedness of types of method parameters
    mparams' <- mapM typecheck mparams
    mtype' <- typecheck mtype

    -- extend environment with method parameters and typecheck body
    mbody' <- local (addParameters mparams) $ hasType mbody mtype'

    mapM_ (checkVariableUsage mbody') (map pname mparams')

    return $ mdef {mparams = mparams'
                  ,mtype = mtype'
                  ,mbody = mbody'}

checkShadowing :: Name -> TypecheckM ()
checkShadowing x = do
  shadow <- isBound x
  when shadow $
    tcWarning $ ShadowedVarWarning x

checkVariableUsage :: Expr -> Name -> TypecheckM ()
checkVariableUsage e x =
  unless (e `usesVar` x) $
    tcWarning $ UnusedVariableWarning x

instance Typecheckable Expr where
  doTypecheck e@(BoolLit {}) = return $ setType BoolType e

  doTypecheck e@(IntLit {}) = return $ setType IntType e

  doTypecheck e@(Lambda {params, body}) = do
    params' <- mapM typecheck params
    body' <- local (addParameters params) $ typecheck body

    mapM_ checkShadowing (map pname params')
    mapM_ (checkVariableUsage body') (map pname params')

    let parameterTypes = map ptype params'
        bodyType = getType body'
        funType = Arrow parameterTypes bodyType
    return $ setType funType e{params = params'
                              ,body = body'}

  doTypecheck e@(VarAccess {name}) = do
    ty <- findVar name
    return $ setType ty e

  doTypecheck e@(FieldAccess {target, name}) = do
    target' <- typecheck target
    let targetType = getType target'

    FieldDef {ftype} <- findField targetType name
    return $ setType ftype e{target = target'}

  doTypecheck e@(Assignment {lhs, rhs}) = do
    unless (isLVal lhs) $
      tcError $ NonLValError lhs

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
          tcError $ ImmutableFieldError e
      checkMutability _ = return ()

  doTypecheck e@(MethodCall {target, name, args}) = do
    target' <- typecheck target
    let targetType = getType target'
    MethodDef {mparams, mtype} <- findMethod targetType name
    let paramTypes = map ptype mparams
    args' <- zipWithM hasType args paramTypes
    return $ setType mtype $ e{target = target'
                              ,args = args'}

  doTypecheck e@(FunctionCall {target, args}) = do
    target' <- typecheck target
    let targetType = getType target'
    unless (isArrowType targetType) $
      tcError $ NonArrowTypeError targetType
    let paramTypes = tparams targetType
        resultType = tresult targetType
    args' <- zipWithM hasType args paramTypes

    return $ setType resultType e{target = target'
                                 ,args = args'}

  doTypecheck e@(BinOp {op, lhs, rhs}) = do
    lhs' <- hasType lhs IntType
    rhs' <- hasType rhs IntType
    return $ setType IntType e{lhs = lhs'
                              ,rhs = rhs'}

  doTypecheck e@(Cast {body, ty}) = do
    ty' <- typecheck ty
    body' <- hasType body ty'
    return $ setType ty' e{body = body'
                          ,ty = ty'}

  doTypecheck e@(If {cond, thn, els}) = do
    cond' <- hasType cond BoolType
    thn' <- typecheck thn
    let thnType = getType thn'
    els' <- hasType els thnType
    return $ setType thnType e{cond = cond'
                              ,thn = thn'
                              ,els = els'}

  doTypecheck e@(Let {name, val, body}) = do
    val' <- typecheck val
    let ty = getType val'

    body' <- local (addVariable name ty) $ typecheck body

    checkShadowing name
    checkVariableUsage body' name

    let bodyType = getType body'
    return $ setType bodyType e{val = val'
                               ,body = body'}

  doTypecheck e =
    tcError $ UninferrableError e

hasType :: Expr -> Type -> TypecheckM Expr
hasType e@Null{} expected = do
  unless (isClassType expected) $
    tcError $ PrimitiveNullError expected
  return $ setType expected e
hasType e expected = do
  e' <- typecheck e
  let eType = getType e'
  unless (eType == expected) $
    tcError $ TypeMismatchError eType expected
  return $ setType expected e'

-- Test
buildClass :: String -> ClassDef
buildClass x =
   ClassDef {cname = "D"
           ,fields = [FieldDef {fmod = Val, fname = "g", ftype = IntType}]
           ,methods = [MethodDef {mname = "m", mparams = [Param {pname = "y", ptype = IntType}], mtype = IntType,
                                  mbody = Let {etype = Nothing
                                              ,name  = x
                                              ,val  = VarAccess Nothing "y"
                                              ,body = IntLit Nothing 42
                                              }
                                 }
                      ]}

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
testProgram = Program testClass3 --[testClass1, testClass2, buildClass "z"]
testProgramW = Program [buildClass "z"]

testSuite = do
  putStrLn $ "\n************************************************"
  putStrLn $ "4.1 Add warnings.\n" ++
             "Showing a program with 3 errors and one warning:\n" ++
             "- type checker only catches one error\n" ++
             "- type checker supports backtrace\n"
  putStrLn "Output:"
  putStrLn ""
  putStrLn $ show $ fromLeft undefined (tcProgram testProgram)
  putStrLn ""
  putStrLn ""
  putStrLn $ "4.2 Add warnings.\n" ++
             "Showing a program with one warning:\n" ++
             "- type checker supports backtrace\n" ++
             "- type checker shows the warning\n"
  putStrLn ""
  putStrLn ""
  putStrLn $ "class D\n" ++
             "  val g: Int\n" ++
             "  def m(y : Int): Int\n    let x = y\n    in 42\n"
  putStrLn ""
  putStrLn "Output:"
  putStrLn ""
  case tcProgram testProgramW of
    Right (Program (p:[]), (ws:[])) -> (putStrLn $ show p) >> (putStrLn $ show ws)
    Left _ -> putStrLn "ERROR"

  putStrLn $ "************************************************"
