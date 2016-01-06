module Q

import Data.HVect
import Data.Vect

unsafeIndex : Int -> List a -> a
unsafeIndex 0 (x::xs) = x
unsafeIndex n (x::xs) = unsafeIndex (n-1) xs

throwError : a -> Either a b
throwError = Left

infixl 9 ..
(..) : (c -> d) -> (a -> b -> c) -> a -> b -> d
(..) f g = \a, b => f (g a b)


data Name = Global String
          | Local Int
          | Quote Int


instance Eq Name where
  (==) (Global x) (Global y) = x == y
  (==) (Local m) (Local n) = m == n
  (==) (Quote m) (Quote n) = m == n
  (==) a b = False


mutual
  data Value = VLam (Value -> Value)
             | VStar
             | VPi Value (Value -> Value)
             | VNeutral Neutral
             | VNat
             | VZero
             | VSucc Value

  data Neutral = NFree Name
               | NApp Neutral Value
               | NNatElim Value Value Value Neutral

Ty : Type
Ty = Value

Env : Type
Env = List Value


mutual
  -- checkable
  data TermDown = Inf TermUp
                | Lam TermDown
  -- inferrable
  data TermUp = Ann TermDown TermDown
              | Star
              | Pi TermDown TermDown
              | Bound Int
              | Free Name
              | At TermUp TermDown
              | TNat
              | NatElim TermDown TermDown TermDown TermDown
              | Zero
              | Succ TermDown

  termDownEq : TermDown -> TermDown -> Bool
  termDownEq (Inf a) (Inf b) = termUpEq a b
  termDownEq (Lam a) (Lam b) = termDownEq a b
  termDownEq _ _ = False

  termUpEq : TermUp -> TermUp -> Bool
  termUpEq (Ann a b) (Ann a' b') = termDownEq a a' && termDownEq b b'
  termUpEq Star Star = True
  termUpEq (Pi a b) (Pi a' b') = termDownEq a a' && termDownEq b b'
  termUpEq (Bound a) (Bound a') = a == a'
  termUpEq (Free a) (Free a') = a == a'
  termUpEq (At a b) (At a' b') = termUpEq a a' && termDownEq b b'
  termUpEq _ _ = False

  instance Eq TermDown where
    (==) = assert_total termDownEq
    (/=) = assert_total (not .. termDownEq)

  instance Eq TermUp where
    (==) = assert_total termUpEq
    (/=) = assert_total (not .. termUpEq)

Context : Type
Context = List (Name, Ty)

Result : Type -> Type
Result a = Either String a


vfree : Name -> Value
vfree n = VNeutral (NFree n)

vapp : Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)


mutual
  rec : TermDown -> Env -> Value -> Value -> Value -> Value
  rec m d mzVal msVal kVal = case kVal of
    VZero => mzVal
    VSucc l => vapp (vapp msVal l) (rec m d mzVal msVal l)
    VNeutral k => VNeutral (NNatElim (evalDown m d) mzVal msVal k)

  evalUp : TermUp -> Env -> Value
  evalUp (Ann e _) d = evalDown e d
  evalUp Star d = VStar
  evalUp (Pi t t') d = VPi (evalDown t d) (\x => evalDown t' (x :: d))
  evalUp (Free x) d = vfree x
  evalUp (Bound i) d = unsafeIndex i d
  evalUp (At e e') d = vapp (evalUp e d) (evalDown e' d)
  evalUp TNat d = VNat
  evalUp Zero d = VZero
  evalUp (Succ k) d = VSucc (evalDown k d)
  evalUp (NatElim m mz ms k) d = let
    mzVal = evalDown mz d
    msVal = evalDown ms d
    in rec m d mzVal msVal (evalDown k d)

  evalDown : TermDown -> Env -> Value
  evalDown (Inf i) d = evalUp i d
  evalDown (Lam e) d = VLam (\x => evalDown e (x::d))


mutual
  substUp : Int -> TermUp -> TermUp -> TermUp
  substUp i r (Ann e t) = Ann (substDown i r e) (substDown i r t)
  substUp i r Star = Star
  substUp i r (Pi t t') = Pi (substDown i r t) (substDown (i+1) r t')
  substUp i r (Bound j) = if i == j then r else Bound j
  substUp i r (Free y) = Free y
  substUp i r (At e e') = At (substUp i r e) (substDown i r e')

  substDown : Int -> TermUp -> TermDown -> TermDown
  substDown i r (Inf e) = Inf (substUp i r e)
  substDown i r (Lam e) = Lam (substDown (i+1) r e)


boundfree : Int -> Name -> TermUp
boundfree i (Quote k) = Bound (i-k-1)
boundfree i x = Free x


mutual
  quote : Int -> Value -> TermDown
  quote i (VLam f) = Lam (quote (i + 1) (f (vfree (Quote i))))
  quote i VStar = Inf Star
  quote i (VPi v f) = Inf (Pi (quote i v) (quote (i+1) (f (vfree (Quote i)))))
  quote i (VNeutral n) = Inf (neutralQuote i n)

  neutralQuote : Int -> Neutral -> TermUp
  neutralQuote i (NFree x) = boundfree i x
  neutralQuote i (NApp n v) = At (neutralQuote i n) (quote i v)


mutual
  typeUp : Int -> Context -> TermUp -> Result Ty
  typeUp i d (Ann e p) = do
    typeDown i d p VStar
    let t = evalDown p []
    typeDown i d e t
    return t
  typeUp i d Star = return VStar
  typeUp i d (Pi p p') = do
    typeDown i d p VStar
    let t = evalDown p []
    typeDown (i+1) ((Local i, t) :: d)
             (substDown 0 (Free (Local i)) p') VStar
    return VStar
  typeUp i d (Free x) = case lookup x d of
    Just t => return t
    Nothing => throwError "unknown identifier"
  typeUp i d (At e e') = do
    s <- typeUp i d e
    case s of
      VPi t t' => do
        typeDown i d e' t
        return (t' (evalDown e' []))
      _ => throwError "illegal application"
  typeUp i d TNat = return VStar
  typeUp i d Zero = return VNat
  typeUp i d (Succ k) = do
    typeDown i d k VNat
    return VNat
  typeUp i d (NatElim m mz ms k) = do
    typeDown i d m (VPi VNat (const VStar))
    let mVal = evalDown m []
    typeDown i d mz (vapp mVal VZero)
    typeDown i d ms (VPi VNat (\l => VPi (vapp mVal l) (\_ => vapp mVal (VSucc l))))
    typeDown i d k VNat
    let kVal = evalDown k []
    return (vapp mVal kVal)

  typeDown : Int -> Context -> TermDown -> Ty -> Result ()
  typeDown i d (Inf e) t = do
    t' <- typeUp i d e
    (when (not ((Q.quote 0 t) == (Q.quote 0 t'))) (throwError "type mismatch"))
  typeDown i d (Lam e) (VPi t t') =
    typeDown (i+1)
             ((Local i, t) :: d)
             (substDown 0 (Free (Local i)) e) (t' (vfree (Local i)))
  typeDown i d _ _ = throwError "type mismatch"

plus : TermDown -> TermUp
plus = NatElim
  (Inf $ Q.Pi (Inf TNat) (Inf TNat))
  (Lam (Inf (Bound 0)))
  (Lam (Lam (Lam (Inf (Succ (Inf (At (Bound 1) (Inf (Bound 0)))))))))

one : TermUp
one = Succ (Inf Zero)

plusOne : TermUp
plusOne = plus (Inf one)

onePlusOne : TermUp
onePlusOne = At plusOne (Inf one)
