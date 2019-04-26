{-# LANGUAGE NamedFieldPuns, TypeSynonymInstances, FlexibleInstances,
FlexibleContexts, RankNTypes, DataKinds, GADTs #-}

module PhantomPhases.Typechecker where

import Data.Map as Map hiding (foldl, map, null, (\\))
import Data.List as List
import Text.Printf (printf)
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except
import PhantomPhases.AST

-- Errors
data TCError where
  DuplicateClassError  ::  Name -> TCError
  UnknownClassError    ::  Name -> TCError
  UnknownFieldError    ::  Name -> TCError
  UnknownMethodError   ::  Name -> TCError
  UnboundVariableError ::  Name -> TCError
  TypeMismatchError    ::  Type 'Checked -> Type 'Checked -> TCError
  ImmutableFieldError  ::  Expr 'Checked -> TCError
  NonLValError         ::  Expr 'Checked -> TCError
  PrimitiveNullError   ::  Type 'Checked -> TCError
  NonClassTypeError    ::  Type p -> TCError
  NonArrowTypeError    ::  Type 'Checked -> TCError
  UninferrableError    ::  Expr 'Parsed -> TCError

instance Show TCError where
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
  Env {ctable :: Map Name ClassEntry
      ,vartable :: Map Name (Type 'Checked) }

lookupClass :: Name -> Env -> Maybe ClassEntry
lookupClass c Env{ctable} = Map.lookup c ctable

lookupVar :: Name -> Env -> Maybe (Type 'Checked)
lookupVar x Env{vartable} = Map.lookup x vartable

-- Lookup functions with error messages
findClass :: Type p -> TypecheckM ClassEntry
findClass (ClassType c) = do
  cls <- asks $ lookupClass c
  case cls of
    Just cdef -> return cdef
    Nothing -> throwError $ UnknownClassError c
findClass ty = throwError $ NonClassTypeError ty

findMethod :: Type p1 -> Name -> TypecheckM MethodEntry
findMethod ty m = do
  ClassEntry{cemethods} <- findClass ty
  case Map.lookup m cemethods of
    Just entry -> return entry
    Nothing -> throwError $ UnknownMethodError m

findField :: Type p1 -> Name -> TypecheckM FieldEntry
findField ty f = do
  ClassEntry{cefields} <- findClass ty
  case Map.lookup f cefields of
    Just entry -> return entry
    Nothing -> throwError $ UnknownFieldError f

findVar :: Name -> TypecheckM (Type 'Checked)
findVar x = do
  result <- asks $ lookupVar x
  case result of
    Just t -> return t
    Nothing -> throwError $ UnboundVariableError x

generateEnvironment :: Program 'Parsed -> Except TCError Env
generateEnvironment (Program classes) = do
  classEntries <- mapM precheckClass classes
  let cnames = map cname classes
      duplicates = cnames \\ nub cnames
  unless (null duplicates) $
    throwError $ DuplicateClassError (head duplicates)
  return $ Env {ctable = Map.fromList $
                         zip cnames classEntries
               ,vartable = Map.empty
               }
  where
    precheckClass :: ClassDef 'Parsed -> Except TCError ClassEntry
    precheckClass ClassDef {fields, methods} = do
      fields' <- mapM precheckField fields
      methods' <- mapM precheckMethod methods
      return ClassEntry {cefields = Map.fromList $
                                    zip (map fname fields) fields'
                        ,cemethods = Map.fromList $
                                     zip (map mname methods) methods'}

    precheckField :: FieldDef 'Parsed -> Except TCError FieldEntry
    precheckField FieldDef {ftype, fmod} = do
      ftype' <- precheckType ftype
      return FieldEntry {femod = fmod
                        ,fetype = ftype'
                        }

    precheckParam :: Param 'Parsed -> Except TCError (Param 'Checked)
    precheckParam Param {ptype, pname} = do
      ptype' <- precheckType ptype
      return Param {pname
                   ,ptype = ptype'}

    precheckMethod :: MethodDef 'Parsed -> Except TCError MethodEntry
    precheckMethod MethodDef {mparams, mtype} = do
      mtype' <- precheckType mtype
      mparams' <- mapM precheckParam mparams
      return $ MethodEntry {meparams = mparams'
                           ,metype = mtype'}

    precheckType :: Type 'Parsed -> Except TCError (Type 'Checked)
    precheckType (ClassType c) = do
      unless (any ((== c) . cname) classes) $
        throwError $ UnknownClassError c
      return $ ClassType c
    precheckType IntType = return IntType
    precheckType BoolType = return BoolType
    precheckType UnitType = return UnitType
    precheckType (Arrow ts t) = do
      ts' <- mapM precheckType ts
      t' <- precheckType t
      return $ Arrow ts' t'

addVariable :: Name -> Type 'Checked -> Env -> Env
addVariable x t env@Env{vartable} =
  env{vartable = Map.insert x t vartable}

addParameters :: [Param 'Checked] -> Env -> Env
addParameters params env = foldl addParameter env params
  where
    addParameter env (Param name ty) = addVariable name ty env

type TypecheckM a = forall m. (MonadReader Env m, MonadError TCError m) => m a

tcProgram :: Program 'Parsed -> Either TCError (Program 'Checked)
tcProgram p = do
  env <- runExcept $ generateEnvironment p
  let exceptM = runReaderT (typecheck p) env
  runExcept exceptM

class Typecheckable a where
  typecheck :: a 'Parsed -> TypecheckM (a 'Checked)

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
  typecheck (Program classes) =  Program <$> (mapM typecheck classes)

instance Typecheckable ClassDef where
  typecheck ClassDef{cname, fields, methods} = do
    fields' <- local (addVariable thisName (ClassType cname)) $ mapM typecheck fields
    methods' <- local (addVariable thisName (ClassType cname)) $ mapM typecheck methods
    return $ ClassDef {fields = fields'
                      ,cname
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
  typecheck MethodDef {mname, mparams, mbody, mtype} = do
    -- typecheck the well-formedness of types of method parameters
    mparams' <- mapM typecheck mparams
    mtype' <- typecheck mtype

    -- extend environment with method parameters and typecheck body
    mbody' <- local (addParameters mparams') $ hasType mbody mtype'
    return $ MethodDef {mname
                       ,mparams = mparams'
                       ,mtype = mtype'
                       ,mbody = mbody'}

instance Typecheckable Expr where
  typecheck BoolLit {bval} = return $ BoolLit (Just BoolType) bval

  typecheck IntLit {ival} = return $ IntLit (Just IntType) ival

  typecheck (Lambda {params, body}) = do
    params' <- mapM typecheck params
    body' <- local (addParameters params') $ typecheck body
    let parameterTypes = map ptype params'
        bodyType = getType body'
        funType = Arrow parameterTypes bodyType
    return $ Lambda {etype = Just funType
                    ,params = params'
                    ,body = body'}

  typecheck (VarAccess {name}) = do
    ty <- findVar name
    return $ VarAccess {etype = Just ty
                       ,name}

  typecheck (FieldAccess {target, name}) = do
    target' <- typecheck target
    let targetType = getType target'

    FieldEntry {fetype} <- findField targetType name
    return $ FieldAccess{target = target'
                        ,etype = Just fetype
                        ,name }

  typecheck (Assignment {lhs, rhs}) = do
    lhs' <- typecheck lhs
    unless (isLVal lhs') $
      throwError $ NonLValError lhs'
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
          throwError $ ImmutableFieldError e
      checkMutability _ = return ()

  typecheck MethodCall {target, name, args} = do
    target' <- typecheck target
    let targetType = getType target'
    MethodEntry {meparams, metype} <- findMethod targetType name

    let paramTypes = map ptype meparams
    args' <- zipWithM hasType args paramTypes

    return $ MethodCall {target = target'
                        ,etype = Just metype
                        ,name
                        ,args = args'}

  typecheck (FunctionCall {target, args}) = do
    target' <- typecheck target
    let targetType = getType target'
    unless (isArrowType targetType) $
      throwError $ NonArrowTypeError targetType
    let paramTypes = tparams targetType
        resultType = tresult targetType
    args' <- zipWithM hasType args paramTypes

    return $ FunctionCall {etype = Just resultType
                          ,target = target'
                          ,args = args'}

  typecheck (BinOp {op, lhs, rhs}) = do
    lhs' <- hasType lhs IntType
    rhs' <- hasType rhs IntType
    return $ BinOp {etype = Just IntType
                   ,op
                   ,lhs = lhs'
                   ,rhs = rhs'}

  typecheck (Cast {body, ty}) = do
    ty' <- typecheck ty
    body' <- hasType body ty'
    return $ Cast {etype = Just ty'
                  ,body = body'
                  ,ty = ty'}

  typecheck (If {cond, thn, els}) = do
    cond' <- hasType cond BoolType
    thn' <- typecheck thn
    let thnType = getType thn'
    els' <- hasType els thnType
    return $ If {etype = Just thnType
                ,cond = cond'
                ,thn = thn'
                ,els = els'}

  typecheck (Let {name, val, body}) = do
    val' <- typecheck val
    let ty = getType val'
    body' <- local (addVariable name ty) $ typecheck body
    let bodyType = getType body'
    return $ Let{etype = Just bodyType
                ,name
                ,val = val'
                ,body = body'}

  typecheck e =
    throwError $ UninferrableError e

hasType :: Expr 'Parsed -> Type 'Checked -> TypecheckM (Expr 'Checked)
hasType Null{} expected = do
  unless (isClassType expected) $
    throwError $ PrimitiveNullError expected
  return $ Null {etype = Just expected}
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
