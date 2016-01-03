module Q

import Data.HVect
import Data.Vect


data QTypeFlag = QTFNull
               | QTFNumber
               | QTFString
               | QTFBoolean
               | QTFUnion
               | QTFIntersection
               | QTFFunction
               | QTFTypeVariable
               | QTFTypeFunction


data QType : QTypeFlag -> Type where
  QTNull               : QType QTFNull
  QTNumber             : QType QTFNumber
  QTString             : QType QTFString
  QTBoolean            : QType QTFBoolean
  QTEmptyUnion         : QType QTFUnion
  QTUnion              : QType a
                      -> QType QTFUnion
                      -> QType QTFUnion
  QTEmptyIntersection  : QType QTFIntersection
  QTIntersection       : QType a
                      -> QType QTFIntersection
                      -> QType QTFIntersection
  QTFunction           : QType a
                      -> QType b
                      -> QType QTFFunction
  QTTypeVariable       : Nat
                      -> QType QTFTypeVariable
  QTTypeFunction       : (f : QTypeFlag -> QTypeFlag)
                      -> ({a : QTypeFlag} -> QType a -> QType (f a))
                      -> QType QTFTypeFunction


data QTypeVariable = TypeVariable String -- string had better be fucking unique


-- data Unification = UnificatinoNo
--                  | UnificationYes (List (QTypeVariable, (f :: QType f)))


data QValue : QType flag -> Type where
  QNull               : QValue QTNull
  QNumber             : Double
                     -> QValue QTNumber
  QString             : String
                     -> QValue QTString
  QBoolean            : Bool
                     -> QValue QTBoolean
  QEmptyUnion         : QValue QTEmptyUnion
  QUnion              : (x : QValue a)
                     -> QValue u
                     -> QValue (QTUnion a u)
  QEmptyIntersection  : QValue QTEmptyIntersection
  QIntersectionHere   : (x : QValue a)
                     -> QValue u
                     -> QValue (QTIntersection a u)
  QIntersectionThere  : QValue (QTIntersection a b)
                     -> QValue (QTIntersection c (QTIntersection a b))
  QFunction           : (QValue a -> QValue f)
                     -> QValue (QTFunction a f)


data QExpression : (t : QType flag) -> Type where
  QNeutral : QValue t -> QExpression t
  QLambda : QValue a -> QExpression (QTFunction a t) -> QExpression t


eval : QExpression t -> QValue t
eval (QNeutral v) = v
eval (QLambda a f) = let QFunction f' = eval f in f' a


instance Show (QValue t) where
  show (QNumber n) = show n
  show (QString s) = show s
  show (QBoolean b) = show b
  show (QEmptyUnion) = "()"
  show (QUnion v u) = "(" ++ show v ++ ", " ++ show u ++ ")"
  show (QEmptyIntersection) = "[]"
  show (QIntersectionHere v i) = "[" ++ show v ++ ", " ++ show i ++ "]"
  show (QIntersectionThere i) = "[, " ++ show i ++ "]"
  show (QFunction f) = "a function"


qUnion : {flags : Vect n QTypeFlag} -> HVect (map QType flags) -> QType QTFUnion
qUnion {flags=Nil} Nil = QTEmptyUnion
qUnion {flags=t::ts} (x::xs) = QTUnion x (qUnion xs)

qIntersection : {flags : Vect n QTypeFlag} -> HVect (map QType flags) -> QType QTFIntersection
qIntersection {flags=Nil} Nil = QTEmptyIntersection
qIntersection {flags=t::ts} (x::xs) = QTIntersection x (qIntersection xs)


Library : (a : QTypeFlag ** (t : QType a ** QValue t))
Library = (QTFNumber ** (QTNumber ** QNumber 3))
