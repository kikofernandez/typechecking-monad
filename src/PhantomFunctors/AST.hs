{-# LANGUAGE NamedFieldPuns, KindSignatures, DataKinds, GADTs, PolyKinds #-}

module PhantomFunctors.AST where

import Data.List
import Data.Functor.Identity
import Data.Proxy
import Text.Printf (printf)

type Name = String

data Type (p1 :: Phase f) =
    ClassType Name
  | IntType
  | BoolType
  | Arrow {tparams :: [Type p1], tresult :: Type p1}
  | UnitType
    deriving (Eq)

instance Show (Type p1) where
  show (ClassType c) = c
  show IntType = "int"
  show BoolType = "bool"
  show (Arrow ts t) = "(" ++ commaSep ts ++ ")" ++ " -> " ++ show t
  show UnitType = "unit"

newtype Program (ip :: Phase f) = Program [ClassDef ip] deriving (Show)

data Phase (f :: * -> *) where
  Parsed :: Phase Proxy
  Checked :: Phase Identity

data ClassDef (ip :: Phase f) =
  ClassDef {cname   :: Name
           ,fields  :: [FieldDef ip]
           ,methods :: [MethodDef ip]
           }

instance Show (ClassDef ip) where
  show ClassDef {cname, fields, methods} =
    "class " ++ cname ++ concatMap show fields ++ concatMap show methods ++ "end"

data Mod = Var | Val deriving (Eq)

instance Show Mod where
  show Var = "var"
  show Val = "val"

data FieldDef (p1 :: Phase f) =
  FieldDef {fname :: Name
           ,ftype :: Type p1
           ,fmod  :: Mod
           }

isValField :: FieldDef p1 -> Bool
isValField FieldDef{fmod} = fmod == Val

isVarField :: FieldDef p1 -> Bool
isVarField = not . isValField

instance Show (FieldDef p1) where
  show FieldDef{fname, ftype, fmod} =
    show fmod ++ " " ++ fname ++ " : " ++ show ftype

data Param (p1 :: Phase f) = Param {pname :: Name
                                 ,ptype :: Type p1
                                 }

instance Show (Param p1) where
  show Param{pname, ptype} = pname ++ " : " ++ show ptype

data MethodDef (ip :: Phase f)  =
  MethodDef {mname :: Name
            ,mparams :: [Param ip]
            ,mtype :: Type ip
            ,mbody :: Expr ip
            }

commaSep :: Show t => [t] -> String
commaSep = intercalate ", " . map show

instance Show (MethodDef ip) where
  show MethodDef{mname, mparams, mtype, mbody} =
    "def " ++ mname ++ "(" ++ commaSep mparams ++ ") : " ++
      show mtype ++ show mbody

data Op = Add | Sub | Mul | Div deriving (Eq)

instance Show Op where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"

data Expr (p1 :: Phase f) =
    BoolLit {etype :: f (Type p1)
            ,bval  :: Bool
            }
  | IntLit {etype :: f (Type p1)
           ,ival  :: Int
           }
  | Null {etype :: f (Type p1)
         }
  | Lambda {etype :: f (Type p1)
           ,params :: [Param p1]
           ,body  :: Expr p1
           }
  | VarAccess {etype :: f (Type p1)
              ,name  :: Name
              }
  | FieldAccess {etype  :: f (Type p1)
                ,target :: Expr p1
                ,name   :: Name
                }
  | Assignment {etype :: f (Type p1)
               ,lhs   :: Expr p1
               ,rhs   :: Expr p1
               }
  | MethodCall {etype  :: f (Type p1)
               ,target :: Expr p1
               ,name   :: Name
               ,args   :: [Expr p1]
               }
  | FunctionCall {etype :: f (Type p1)
                 ,target :: Expr p1
                 ,args  :: [Expr p1]
                 }
  | If {etype :: f (Type p1)
       ,cond  :: Expr p1
       ,thn   :: Expr p1
       ,els   :: Expr p1
       }
  | Let {etype :: f (Type p1)
        ,name  :: Name
        ,val  :: Expr p1
        ,body  :: Expr p1
        }
  | BinOp {etype :: f (Type p1)
          ,op    :: Op
          ,lhs   :: Expr p1
          ,rhs   :: Expr p1
          }
  | Cast {etype :: f (Type p1)
         ,body  :: Expr p1
         ,ty    :: (Type p1)
         }

thisName :: Name
thisName = "this"

isArrowType :: (Type p1) -> Bool
isArrowType Arrow {} = True
isArrowType _ = False

isFieldAccess :: Expr p1 -> Bool
isFieldAccess FieldAccess{} = True
isFieldAccess _ = False

isVarAccess :: Expr p1 -> Bool
isVarAccess VarAccess{} = True
isVarAccess _ = False

isLVal :: Expr p1 -> Bool
isLVal e = isFieldAccess e || isVarAccess e

instance Show (Expr p1) where
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

isClassType :: Type p1 -> Bool
isClassType (ClassType _) = True
isClassType _ = False

getType :: Expr 'Checked -> Type 'Checked
getType e = runIdentity (etype e)

setType :: Type 'Checked -> Expr 'Checked -> Expr 'Checked
setType t e = e{etype = Identity t}
