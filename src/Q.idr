module Q

import Data.HVect
import Data.Vect


data TypeFlag = TFNull
              | TFNumber
              | TFString
              | TFBoolean
              | TFTypeVariable
              | TFQuantify
              | TFFunction
              | TFUnion
              | TFIntersection

data QType : Nat -> TypeFlag -> Type where
  QTNull               : QType 0 TFNull
  QTNumber             : QType 0 TFNumber
  QTString             : QType 0 TFString
  QTBoolean            : QType 0 TFBoolean
  QTTypeVariable       : (n : Nat)
                      -> QType (S n) TFTypeVariable
  QTQuantify           : QType (S n) f
                      -> QType n TFQuantify
  QFunction            : QType m a
                      -> QType n b
                      -> QType (Nat.maximum m n) TFFunction
  QTEmptyUnion         : QType 0 TFUnion
  QTUnion              : QType m a
                      -> QType n TFUnion
                      -> QType (Nat.maximum m n) TFUnion
  QTEmptyIntersection  : QType 0 TFIntersection
  QTIntersection       : QType m a
                      -> QType n TFIntersection
                      -> QType (Nat.maximum m n) TFIntersection

fold : (t -> acc -> acc) -> acc -> Vect n t -> acc
fold f e [] = e
fold f e (x::xs) = f x (fold f e xs)

unwrapFold : (a : Nat) -> (b : Nat) -> Nat.maximum a b = fold Nat.maximum 0 [a, b]
unwrapFold Z Z = Refl
unwrapFold Z (S k) = Refl
unwrapFold (S k) Z = Refl
unwrapFold (S k) (S j) = Refl

maxAAA : (a : Nat) -> a = Nat.maximum a a
maxAAA Z = Refl
maxAAA (S k) = cong $ maxAAA k

juice : (a : Nat) -> a = fold Nat.maximum 0 [a, a]
juice x = trans (maxAAA x) (unwrapFold x x)

maximumSuccessor : (a : Nat) -> (b : Nat) -> S (maximum a b) = maximum (S a) (S b)
maximumSuccessor x y = Refl

qUnion  : {freeVars : Vect n Nat}
       -> {flags : Vect n TypeFlag}
       -> HVect (pure QType <*> freeVars <*> flags)
       -> QType (fold Nat.maximum 0 freeVars) TFUnion
qUnion {freeVars=Nil} {flags=Nil} Nil = QTEmptyUnion
qUnion {freeVars=v::vs} {flags=t::ts} (x::xs) = QTUnion x (qUnion xs)

qIntersection  : {freeVars : Vect n Nat}
              -> {flags : Vect n TypeFlag}
              -> HVect (pure QType <*> freeVars <*> flags)
              -> QType (fold Nat.maximum 0 freeVars) TFIntersection
qIntersection {freeVars=Nil} {flags=Nil} Nil = QTEmptyIntersection
qIntersection {freeVars=v::vs} {flags=t::ts} (x::xs) = QTIntersection x (qIntersection xs)

qList : (n : Nat) -> QType (S n) TFIntersection
qList n = qIntersection {freeVars=[0,S n]} {flags=[TFNull, TFUnion]} [QTNull, qListUnion]
  where
  qListUnion : QType (S n) TFUnion
  qListUnion = rewrite juice (S n) in qUnion {freeVars=[S n,S n]} {flags=[TFTypeVariable, TFIntersection]} [QTTypeVariable n, qList n]

qMap : (a : Nat) -> (b : Nat) -> QType (S (Nat.maximum a b)) TFFunction
qMap v1 v2 = rewrite trans (maximumSuccessor v1 v2) (maxAAA (maximum (S v1) (S v2))) in QFunction (QFunction (QTTypeVariable v1) (QTTypeVariable v2)) (QFunction (qList v1) (qList v2))



-- qListType : QType 0 QTFUnion
-- qMapType : QType 0 QTFFunction


-- data Unification : QType a f -> QType b f -> Type where
--   UnifyIdentity : Unification t t
--   UnifyXY : Unification (QTypeVariable x) (QTypeVariable y)




  -- QTFunction           : QType a
  --                     -> QType b
  --                     -> QType QTFFunction
  -- QTTypeVariable       : Nat
  --                     -> QType QTFTypeVariable
  -- QTTypeFunction       : (f : QTypeFlag -> QTypeFlag)
  --                     -> ({a : QTypeFlag} -> QType a -> QType (f a))
  --                     -> QType QTFTypeFunction
  


-- data QTypeVariable = TypeVariable String -- string had better be fucking unique


-- data Unification = UnificatinoNo
--                  | UnificationYes (List (QTypeVariable, (f :: QType f)))


-- data QValue : QType flag -> Type where
--   QNull               : QValue QTNull
--   QNumber             : Double
--                      -> QValue QTNumber
--   QString             : String
--                      -> QValue QTString
--   QBoolean            : Bool
--                      -> QValue QTBoolean
--   QEmptyUnion         : QValue QTEmptyUnion
--   QUnion              : (x : QValue a)
--                      -> QValue u
--                      -> QValue (QTUnion a u)
--   QEmptyIntersection  : QValue QTEmptyIntersection
--   QIntersectionHere   : (x : QValue a)
--                      -> QValue u
--                      -> QValue (QTIntersection a u)
--   QIntersectionThere  : QValue (QTIntersection a b)
--                      -> QValue (QTIntersection c (QTIntersection a b))
--   QFunction           : (QValue a -> QValue f)
--                      -> QValue (QTFunction a f)


-- data QExpression : (t : QType flag) -> Type where
--   QNeutral : QValue t -> QExpression t
--   QLambda : QValue a -> QExpression (QTFunction a t) -> QExpression t


-- eval : QExpression t -> QValue t
-- eval (QNeutral v) = v
-- eval (QLambda a f) = let QFunction f' = eval f in f' a


-- instance Show (QValue t) where
--   show (QNumber n) = show n
--   show (QString s) = show s
--   show (QBoolean b) = show b
--   show (QEmptyUnion) = "()"
--   show (QUnion v u) = "(" ++ show v ++ ", " ++ show u ++ ")"
--   show (QEmptyIntersection) = "[]"
--   show (QIntersectionHere v i) = "[" ++ show v ++ ", " ++ show i ++ "]"
--   show (QIntersectionThere i) = "[, " ++ show i ++ "]"
--   show (QFunction f) = "a function"



-- Library : (a : QTypeFlag ** (t : QType a ** QValue t))
-- Library = (QTFNumber ** (QTNumber ** QNumber 3))
