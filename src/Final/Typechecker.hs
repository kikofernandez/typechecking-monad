{-# LANGUAGE NamedFieldPuns, TypeSynonymInstances, FlexibleInstances,
FlexibleContexts, RankNTypes, DataKinds, GADTs, GeneralizedNewtypeDeriving,
MultiParamTypeClasses, FunctionalDependencies #-}

module Final.Typechecker where

import Data.Map as Map hiding (foldl, map, null, (\\))
import Data.List as List
import Data.List.NonEmpty(NonEmpty)
import Data.Maybe(isJust)
import qualified Data.List.NonEmpty as NE
import Text.Printf (printf)
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Writer
import Final.AST

type TypecheckM a = forall m. (MonadReader Env m,
                               MonadError TCErrors m,
                               MonadWriter [TCWarning] m) => m a

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

data TCWarning = TCWarning Warning Backtrace
data Warning =
    ShadowedVarWarning Name
  | UnusedVariableWarning Name

tcError :: Error -> TypecheckM a
tcError err = do
  bt <- asks bt
  throwError $ TCErrors (NE.fromList [TCError err bt])

tcWarning :: Warning -> TypecheckM ()
tcWarning wrn = do
  bt <- asks bt
  tell $ [TCWarning wrn bt]

-- Errors
data Error where
  DuplicateClassError  ::  Name -> Error
  UnknownClassError    ::  Name -> Error
  UnknownFieldError    ::  Name -> Error
  UnknownMethodError   ::  Name -> Error
  UnboundVariableError ::  Name -> Error
  TypeMismatchError    ::  Type p1 -> Type p1 -> Error
  ImmutableFieldError  ::  Expr p1 -> Error
  NonLValError         ::  Expr p1 -> Error
  PrimitiveNullError   ::  Type p1 -> Error
  NonClassTypeError    ::  Type p1 -> Error
  NonArrowTypeError    ::  Type p1 -> Error
  UninferrableError    ::  Expr p1 -> Error

instance Show Error where
  show (DuplicateClassError c)  = printf "Duplicate declaration of class '%s'"  c
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

instance Show TCWarning where
  show (TCWarning wrn bt) =
    " *** Warning during typechecking *** \n" ++
    show wrn ++ "\n" ++ show bt

instance Show Warning where
  show (ShadowedVarWarning x) =
    printf "Variable '%s' shadows previous definition" x
  show (UnusedVariableWarning x) =
    printf "Variable '%s' is never used" x


-- Environment
data MethodEntry =
  MethodEntry {meparams :: [Param 'Checked]
              ,metype   :: Type 'Checked
              }

data FieldEntry =
  FieldEntry {femod  :: Mod
             ,fetype :: Type 'Checked
             }

data ClassEntry =
  ClassEntry {cefields  :: Map Name FieldEntry
             ,cemethods :: Map Name MethodEntry
             }

data Env =
    PreEnv {classes :: [Name]
           ,bt :: Backtrace}
  | Env {ctable :: Map Name ClassEntry
        ,vartable :: Map Name (Type 'Checked)
        ,bt :: Backtrace}

pushBT :: Backtraceable a => a -> Env -> Env
pushBT x env = env{bt = push x (bt env)}

lookupClass :: Name -> Env -> Maybe ClassEntry
lookupClass c Env{ctable} = Map.lookup c ctable
lookupClass _ PreEnv{} = error "Tried to look up a class from a pre-environment"

validClass :: Name -> Env -> Bool
validClass c Env{ctable} = Map.member c ctable
validClass c PreEnv{classes} = c `elem` classes

lookupVar :: Name -> Env -> Maybe (Type 'Checked)
lookupVar x Env{vartable} = Map.lookup x vartable
lookupVar _ PreEnv{} = error "Tried to look up a variable from a pre-environment"

-- Lookup functions with error messages
resolveClass :: Name -> TypecheckM (Type 'Checked)
resolveClass c = do
  isValid <- asks $ validClass c
  unless isValid $
    tcError $ UnknownClassError c
  return (ClassType c)

findClass :: Type p1 -> TypecheckM ClassEntry
findClass (ClassType c) = do
  cls <- asks $ lookupClass c
  case cls of
    Just cdef -> return cdef
    Nothing -> tcError $ UnknownClassError c
findClass ty = tcError $ NonClassTypeError ty

findMethod :: Type p1 -> Name -> TypecheckM MethodEntry
findMethod ty m = do
  ClassEntry{cemethods} <- findClass ty
  case Map.lookup m cemethods of
    Just entry -> return entry
    Nothing -> tcError $ UnknownMethodError m

findField :: Type p1 -> Name -> TypecheckM FieldEntry
findField ty f = do
  ClassEntry{cefields} <- findClass ty
  case Map.lookup f cefields of
    Just entry -> return entry
    Nothing -> tcError $ UnknownFieldError f

findVar :: Name -> TypecheckM (Type 'Checked)
findVar x = do
  result <- asks $ lookupVar x
  case result of
    Just t -> return t
    Nothing -> tcError $ UnboundVariableError x

isBound :: Name -> TypecheckM Bool
isBound = liftM isJust . asks . lookupVar

generatePreEnv :: Program p -> Env
generatePreEnv (Program classes) = PreEnv{classes = map cname classes
                                         ,bt = emptyBt}

class Precheckable a b | a -> b where
  doPrecheck :: a -> TypecheckM b

  precheck :: (Backtraceable a) => a -> TypecheckM b
  precheck x = local (pushBT x) $ doPrecheck x

instance Precheckable (Type p) (Type 'Checked) where
  doPrecheck (ClassType c) = resolveClass c
  doPrecheck IntType = return IntType
  doPrecheck BoolType = return BoolType
  doPrecheck UnitType = return UnitType
  doPrecheck (Arrow ts t) = do
    ts' <- mapM precheck ts
    t' <- precheck t
    return $ Arrow ts' t'

instance Precheckable (FieldDef 'Parsed) FieldEntry where
  doPrecheck FieldDef {ftype, fmod} = do
    ftype' <- precheck ftype
    return FieldEntry {femod = fmod
                      ,fetype = ftype'
                      }

instance Precheckable (Param 'Parsed) (Param 'Checked) where
  doPrecheck Param {ptype, pname} = do
    ptype' <- precheck ptype
    return Param {pname
                 ,ptype = ptype'}

instance Precheckable (MethodDef 'Parsed) MethodEntry where
  doPrecheck MethodDef {mparams, mtype} = do
    mtype' <- precheck mtype
    mparams' <- mapMFork precheck mparams
    return $ MethodEntry {meparams = mparams'
                         ,metype = mtype'}

instance Precheckable (ClassDef 'Parsed) ClassEntry where
  doPrecheck ClassDef {fields, methods} = do
    (fields', methods') <- mapMFork precheck fields <&>
                           mapMFork precheck methods
    return ClassEntry {cefields = Map.fromList $
                                  zip (map fname fields) fields'
                      ,cemethods = Map.fromList $
                                   zip (map mname methods) methods'}

generateEnvironment :: Program 'Parsed -> TypecheckM Env
generateEnvironment (Program classes) = do
  classEntries <- mapMFork precheck classes
  let cnames = map cname classes
      duplicates = cnames \\ nub cnames
  unless (null duplicates) $
    tcError $ DuplicateClassError (head duplicates)
  return $ Env {ctable = Map.fromList $
                         zip cnames classEntries
               ,vartable = Map.empty
               ,bt = emptyBt
               }

addVariable :: Name -> Type 'Checked -> Env -> Env
addVariable x t env@Env{vartable} =
  env{vartable = Map.insert x t vartable}
addVariable _ _ PreEnv{} = error "Tried to insert a variable into a pre-environment"

addParameters :: [Param 'Checked] -> Env -> Env
addParameters params env = foldl addParameter env params
  where
    addParameter env (Param name ty) = addVariable name ty env

tcProgram :: Program 'Parsed -> Either TCErrors (Program 'Checked, [TCWarning])
tcProgram p = do
  let preEnv = generatePreEnv p
  (env, _) <- runExcept $ runReaderT (runWriterT (generateEnvironment p)) preEnv
  let exceptM = runReaderT (runWriterT (doTypecheck p)) env
  runExcept exceptM

class Typecheckable a where
  doTypecheck :: a 'Parsed -> TypecheckM (a 'Checked)

  typecheck :: (Backtraceable (a 'Parsed)) => a 'Parsed -> TypecheckM (a 'Checked)
  typecheck x = local (pushBT x) $ doTypecheck x

-- Type checking the well-formedness of types
instance Typecheckable Type where
  doTypecheck = doPrecheck

instance Typecheckable Program where
  doTypecheck (Program classes) =  Program <$> (mapMFork typecheck classes)

instance Typecheckable ClassDef where
  doTypecheck ClassDef{cname, fields, methods} = do
    (fields', methods') <- local (addVariable thisName (ClassType cname)) $
                           mapMFork typecheck fields <&>
                           mapMFork typecheck methods
    return $ ClassDef {cname
                      ,fields = fields'
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
  doTypecheck MethodDef {mname, mparams, mbody, mtype} = do
    -- typecheck the well-formedness of types of method parameters
    (mparams', mtype') <- mapMFork typecheck mparams <&>
                          typecheck mtype

    -- extend environment with method parameters and typecheck body
    mbody' <- local (addParameters mparams') $ hasType mbody mtype'

    mapM_ (checkVariableUsage mbody') (map pname mparams')

    return $ MethodDef {mname
                       ,mparams = mparams'
                       ,mtype = mtype'
                       ,mbody = mbody'}

checkShadowing :: Name -> TypecheckM ()
checkShadowing x = do
  shadow <- isBound x
  when shadow $
    tcWarning $ ShadowedVarWarning x

checkVariableUsage :: Expr p -> Name -> TypecheckM ()
checkVariableUsage e x =
  unless (e `usesVar` x) $
    tcWarning $ UnusedVariableWarning x


instance Typecheckable Expr where
  doTypecheck BoolLit {bval} = return $ BoolLit (Just BoolType) bval

  doTypecheck IntLit {ival} = return $ IntLit (Just IntType) ival

  doTypecheck (Lambda {params, body}) = do
    params' <- mapMFork typecheck params
    body' <- local (addParameters params') $ typecheck body

    mapM_ checkShadowing (map pname params')
    mapM_ (checkVariableUsage body') (map pname params')

    let parameterTypes = map ptype params'
        bodyType = getType body'
        funType = Arrow parameterTypes bodyType
    return $ Lambda {etype = Just funType
                    ,params = params'
                    ,body = body'}

  doTypecheck (VarAccess {name}) = do
    ty <- findVar name
    return $ VarAccess {etype = Just ty
                       ,name}

  doTypecheck (FieldAccess {target, name}) = do
    target' <- typecheck target
    let targetType = getType target'

    FieldEntry {fetype} <- findField targetType name
    return $ FieldAccess{target = target'
                        ,etype = Just fetype
                        ,name }

  doTypecheck (Assignment {lhs, rhs}) = do
    unless (isLVal lhs) $
      tcError $ NonLValError lhs

    lhs' <- typecheck lhs
    let lType = getType lhs'

    rhs' <- hasType rhs lType
    checkMutability lhs'

    return $ Assignment {etype = Just UnitType
                        ,lhs = lhs'
                        ,rhs = rhs'}
    where
      checkMutability e@FieldAccess{name} = do
        FieldEntry {femod} <- findField (getType e) name
        unless (femod == Var) $
          tcError $ ImmutableFieldError e
      checkMutability _ = return ()

  doTypecheck MethodCall {target, name, args} = do
    target' <- typecheck target
    let targetType = getType target'
    MethodEntry {meparams, metype} <- findMethod targetType name

    let paramTypes = map ptype meparams
    args' <- zipWithM hasType args paramTypes

    return $ MethodCall {target = target'
                        ,etype = Just metype
                        ,name
                        ,args = args'}

  doTypecheck (FunctionCall {target, args}) = do
    target' <- typecheck target
    let targetType = getType target'
    unless (isArrowType targetType) $
      tcError $ NonArrowTypeError targetType
    let paramTypes = tparams targetType
        resultType = tresult targetType
    args' <- zipWithM hasType args paramTypes

    return $ FunctionCall {etype = Just resultType
                          ,target = target'
                          ,args = args'}

  doTypecheck (BinOp {op, lhs, rhs}) = do
    lhs' <- hasType lhs IntType
    rhs' <- hasType rhs IntType
    return $ BinOp {etype = Just IntType
                   ,op
                   ,lhs = lhs'
                   ,rhs = rhs'}

  doTypecheck (Cast {body, ty}) = do
    ty' <- typecheck ty
    body' <- hasType body ty'
    return $ Cast {etype = Just ty'
                  ,body = body'
                  ,ty = ty'}

  doTypecheck (If {cond, thn, els}) = do
    cond' <- hasType cond BoolType
    thn' <- typecheck thn
    let thnType = getType thn'
    els' <- hasType els thnType
    return $ If {etype = Just thnType
                ,cond = cond'
                ,thn = thn'
                ,els = els'}

  doTypecheck (Let {name, val, body}) = do
    val' <- typecheck val
    let ty = getType val'
    body' <- local (addVariable name ty) $ typecheck body

    checkShadowing name
    checkVariableUsage body' name

    let bodyType = getType body'
    return $ Let{etype = Just bodyType
                ,name
                ,val = val'
                ,body = body'}

  doTypecheck e =
    tcError $ UninferrableError e

hasType :: Expr 'Parsed -> Type 'Checked -> TypecheckM (Expr 'Checked)
hasType Null{} expected = do
  unless (isClassType expected) $
    tcError $ PrimitiveNullError expected
  return $ Null {etype = Just expected}
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
