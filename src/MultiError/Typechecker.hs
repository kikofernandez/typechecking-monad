{-# LANGUAGE NamedFieldPuns, TypeSynonymInstances, FlexibleInstances,
FlexibleContexts, RankNTypes, ConstrainedClassMethods,
GeneralizedNewtypeDeriving #-}
module MultiError.Typechecker where

import Data.Map as Map hiding (foldl, map)
import Data.List as List
import Data.Either (fromLeft)
import Data.List.NonEmpty(NonEmpty)
import qualified Data.List.NonEmpty as NE
import Text.Printf (printf)
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except
import MultiError.AST

type TypecheckM a = forall m. (MonadReader Env m, MonadError TCErrors m) => m a

-- <:> is a particular definition of Either as a magma
(<:>) :: Semigroup e => Either e a -> Either e b -> Either e (a, b)
(Right v1) <:> (Right v2) = Right (v1, v2)
(Left e1) <:> (Left e2) = Left $ e1 <> e2
(Left e1) <:> _ = Left e1
_ <:> (Left e2) = Left e2

-- Perform two typechecking actions, fail if one of them fails,
-- and merge their errors if both fail
(<&>) :: (Semigroup e, MonadError e m) => m a -> m b -> m (a, b)
tc1 <&> tc2 = do
  res1 <- (tc1 >>= return . Right) `catchError` (\err -> return $ Left err)
  res2 <- (tc2 >>= return . Right) `catchError` (\err -> return $ Left err)
  liftEither $ res1 <:> res2

-- Allow typechecking a list of items, collecting error messages
-- from all of them
mapMFork :: (Semigroup e, MonadError e m) => (a -> m b) -> [a] -> m [b]
mapMFork _ [] = return []
mapMFork f (x:xs) = uncurry (:) <$> (f x <&> mapMFork f xs)

-- Errors
newtype TCErrors = TCErrors (NonEmpty TCError) deriving (Semigroup)

instance Show TCErrors where
  show (TCErrors errs) =
    " *** Error during typechecking *** \n" ++
    intercalate "\n" (map show (NE.toList errs))

data TCError = TCError Error Backtrace

instance Show TCError where
  show (TCError err bt) = show err ++ "\n" ++ show bt

tcError :: Error -> TypecheckM a
tcError err = do
  bt <- asks bt
  throwError $ TCErrors (NE.fromList [TCError err bt])

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

-- Environment: We do not have a situation where Env <> Env but
--              the Empty Env is a monoid and a semigroup
data Env =
  Env {ctable :: Map Name ClassDef
      ,vartable :: Map Name Type
      ,bt :: Backtrace}

emptyEnv = Env {ctable = Map.empty
               ,vartable = Map.empty
               ,bt = emptyBt}

lookupClass :: Name -> Env -> Maybe ClassDef
lookupClass c Env{ctable} = Map.lookup c ctable

lookupVar :: Name -> Env -> Maybe Type
lookupVar x Env{vartable} = Map.lookup x vartable

-- Lookup functions with error messages
findClass :: Type -> TypecheckM ClassDef
findClass (ClassType c) = do
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

tcProgram :: Program -> Either TCErrors Program
tcProgram p = do
  let env = genEnv p
      exceptM = runReaderT (doTypecheck p) env
  runExcept exceptM

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
    ts' <- mapMFork typecheck ts
    t' <- typecheck t
    return $ Arrow ts' t'

instance Typecheckable Program where
  doTypecheck (Program cls) = Program <$> mapMFork typecheck cls

instance Typecheckable ClassDef where
  doTypecheck cdef@ClassDef{cname, fields, methods} = do
    let withThisAdded = local $ addVariable thisName (ClassType cname)
    (fields', methods') <- withThisAdded $
                           mapMFork typecheck fields <&>
                           mapMFork typecheck methods
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
    (mparams', mtype') <- mapMFork typecheck mparams <&>
                          typecheck mtype

    -- extend environment with method parameters and typecheck body
    mbody' <- local (addParameters mparams) $ hasType mbody mtype'

    return $ mdef {mparams = mparams'
                  ,mtype = mtype'
                  ,mbody = mbody'}

instance Typecheckable Expr where
  doTypecheck e@(BoolLit {}) = return $ setType BoolType e

  doTypecheck e@(IntLit {}) = return $ setType IntType e

  doTypecheck e@(Lambda {params, body}) = do
    params' <- mapMFork typecheck params
    body' <- local (addParameters params) $ typecheck body
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
-- testClass3 =
--   [ClassDef {cname = "D"
--            ,fields = [FieldDef {fmod = Val, fname = "g", ftype = ClassType "D"}]
--            ,methods = [MethodDef {mname = "m", mparams = [], mtype = IntType, mbody = VarAccess Nothing "x"}]},
--    ClassDef {cname = "D"
--            ,fields = [FieldDef {fmod = Val, fname = "g", ftype = ClassType "D"}]
--            ,methods = [MethodDef {mname = "m", mparams = [], mtype = IntType, mbody = VarAccess Nothing "x"}]}]


--testProgram :: Program 'Parsed 'Parsed
testProgram = Program $ [testClass1, testClass2]

testSuite = do
  putStrLn $ "\n************************************************"
  putStrLn $ "5. Multiple errors.\n" ++
             "Showing a program with 3 errors:\n" ++
             "- type checker catches multiple error\n" ++
             "- there is support for backtrace\n"
  putStrLn "Output:"
  putStrLn ""
  putStrLn $ show $ fromLeft undefined (tcProgram testProgram)
  putStrLn ""
  putStrLn $ "************************************************"
