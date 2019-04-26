{-# LANGUAGE NamedFieldPuns, ConstrainedClassMethods, TypeFamilies #-}

module Backtrace.AST where

import Data.Maybe
import Data.List
import Text.Printf (printf)

type Name = String

data Type =
    ClassType Name
  | IntType
  | BoolType
  | Arrow {tparams :: [Type], tresult :: Type}
  | UnitType
    deriving (Eq)

instance Show Type where
  show (ClassType c) = c
  show IntType = "int"
  show BoolType = "bool"
  show (Arrow ts t) = "(" ++ commaSep ts ++ ")" ++ " -> " ++ show t
  show UnitType = "unit"

newtype Program = Program [ClassDef] deriving (Show)

data ClassDef =
  ClassDef {cname   :: Name
           ,fields  :: [FieldDef]
           ,methods :: [MethodDef]
           }

instance Show ClassDef where
  show ClassDef {cname, fields, methods} =
    "class " ++ cname ++ concatMap show fields ++ concatMap show methods ++ "end"

data Mod = Var | Val deriving (Eq)

instance Show Mod where
  show Var = "var"
  show Val = "val"

data FieldDef =
  FieldDef {fname :: Name
           ,ftype :: Type
           ,fmod  :: Mod
           }

isValField :: FieldDef -> Bool
isValField FieldDef{fmod} = fmod == Val

isVarField :: FieldDef -> Bool
isVarField = not . isValField

instance Show FieldDef where
  show FieldDef{fname, ftype, fmod} =
    show fmod ++ " " ++ fname ++ " : " ++ show ftype

data Param = Param {pname :: Name
                   ,ptype :: Type
                   }

instance Show Param where
  show Param{pname, ptype} = pname ++ " : " ++ show ptype

data MethodDef =
  MethodDef {mname :: Name
            ,mparams :: [Param]
            ,mtype :: Type
            ,mbody :: Expr
            }

commaSep :: Show t => [t] -> String
commaSep = intercalate ", " . map show

instance Show MethodDef where
  show MethodDef{mname, mparams, mtype, mbody} =
    "def " ++ mname ++ "(" ++ commaSep mparams ++ ") : " ++
      show mtype ++ show mbody

data Op = Add | Sub | Mul | Div deriving (Eq)

instance Show Op where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"

data Expr =
    BoolLit {etype :: Maybe Type
            ,bval  :: Bool
            }
  | IntLit {etype :: Maybe Type
           ,ival  :: Int
           }
  | Null {etype :: Maybe Type
         }
  | Lambda {etype :: Maybe Type
           ,params :: [Param]
           ,body  :: Expr
           }
  | VarAccess {etype :: Maybe Type
              ,name  :: Name
              }
  | FieldAccess {etype  :: Maybe Type
                ,target :: Expr
                ,name   :: Name
                }
  | Assignment {etype :: Maybe Type
               ,lhs   :: Expr
               ,rhs   :: Expr
               }
  | MethodCall {etype  :: Maybe Type
               ,target :: Expr
               ,name   :: Name
               ,args   :: [Expr]
               }
  | FunctionCall {etype :: Maybe Type
                 ,target :: Expr
                 ,args  :: [Expr]
                 }
  | If {etype :: Maybe Type
       ,cond  :: Expr
       ,thn   :: Expr
       ,els   :: Expr
       }
  | Let {etype :: Maybe Type
        ,name  :: Name
        ,val  :: Expr
        ,body  :: Expr
        }
  | BinOp {etype :: Maybe Type
          ,op    :: Op
          ,lhs   :: Expr
          ,rhs   :: Expr
          }
  | Cast {etype :: Maybe Type
         ,body  :: Expr
         ,ty    :: Type
         }

thisName :: Name
thisName = "this"

isArrowType :: Type -> Bool
isArrowType Arrow {} = True
isArrowType _ = False

isFieldAccess :: Expr -> Bool
isFieldAccess FieldAccess{} = True
isFieldAccess _ = False

isVarAccess :: Expr -> Bool
isVarAccess VarAccess{} = True
isVarAccess _ = False

isLVal :: Expr -> Bool
isLVal e = isFieldAccess e || isVarAccess e

instance Show Expr where
  show BoolLit{bval} = show bval
  show IntLit{ival} = show ival
  show Null{} = "null"
  show Lambda{params, body} =
    printf "fun (%s) => %s" (commaSep params) (show body)
  show VarAccess{name} = name
  show FieldAccess{target, name} =
    printf "%s.%s" (show target) name
  show Assignment{lhs, rhs} =
    printf "%s = %s" (show lhs) (show rhs)
  show MethodCall{target, name, args} =
    printf "%s.%s(%s)" (show target) name (commaSep args)
  show FunctionCall{target, args} =
    printf "%s(%s)" (show target) (commaSep args)
  show If{cond, thn, els} =
    printf "if %s then %s else %s" (show cond) (show thn) (show els)
  show Let{name, val, body} =
    printf "let %s = %s in %s" name (show val) (show body)
  show BinOp{op, lhs, rhs} =
    printf "%s %s %s" (show lhs) (show op) (show rhs)
  show Cast{body, ty} =
    printf "%s : %s" (show body) (show ty)

isClassType :: Type -> Bool
isClassType (ClassType _) = True
isClassType _ = False

getType :: Expr -> Type
getType = fromJust . etype

setType :: Type -> Expr -> Expr
setType t e = e{etype = Just t}

newtype Backtrace = Backtrace [BacktraceNode]

emptyBt :: Backtrace
emptyBt = Backtrace []

data BacktraceNode = BTClass ClassDef
                   | BTParam Param
                   | BTField FieldDef
                   | BTMethod MethodDef
                   | BTExpr Expr
                   | BTType Type

class Backtraceable a where
  backtrace :: a -> BacktraceNode

  push :: a -> Backtrace -> Backtrace
  push x (Backtrace bt) = Backtrace (backtrace x : bt)

instance Backtraceable ClassDef where
  backtrace = BTClass

instance Backtraceable MethodDef where
  backtrace = BTMethod

instance Backtraceable FieldDef where
  backtrace = BTField

instance Backtraceable Param where
  backtrace = BTParam

instance Backtraceable Expr where
  backtrace = BTExpr

instance Backtraceable Type where
  backtrace = BTType

instance Show BacktraceNode where
  show (BTClass ClassDef{cname}) = printf "class '%s'" cname
  show (BTParam p) = printf "parameter '%s'" (show p)
  show (BTField f) = printf "field '%s'" (show f)
  show (BTMethod MethodDef{mname}) = printf "method '%s'" mname
  show (BTExpr e)  = printf "expression %s" (show e)
  show (BTType ty) = printf "type '%s'" (show ty)

instance Show Backtrace where
  show (Backtrace bt) = "In " ++ (intercalate "\nIn " $ map show bt)
