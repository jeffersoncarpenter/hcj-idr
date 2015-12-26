module Q


data QTypeFlag = QTFNumber
               | QTFString
               | QTFBoolean
               | QTFUnion
               | QTFIntersection
               | QTFFunction


data QType : QTypeFlag -> Type where
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
                      

data QValue : QType flag -> Type where
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
  

-- strings
str : QValue QTString
str = QString "aoeu"

-- numbers
num : QValue QTNumber
num = QNumber 2


-- unions
StringUnion : QType QTFUnion
StringUnion = QTUnion QTString QTEmptyUnion

StringNumberUnion : QType QTFUnion
StringNumberUnion = (QTUnion QTNumber StringUnion)

emptyUnion : QValue QTEmptyUnion
emptyUnion = QEmptyUnion

stringUnion : QValue StringUnion
stringUnion = QUnion str emptyUnion

stringNumberUnion : QValue StringNumberUnion
stringNumberUnion = QUnion num (QUnion str emptyUnion)


-- intersections
StringIntersection : QType QTFIntersection
StringIntersection = QTIntersection QTString QTEmptyIntersection

StringNumberIntersection : QType QTFIntersection
StringNumberIntersection = QTIntersection QTNumber StringIntersection

emptyIntersection : QValue QTEmptyIntersection
emptyIntersection = QEmptyIntersection

stringIntersection : QValue StringIntersection
stringIntersection = QIntersectionHere str QEmptyIntersection

stringNumberIntersection : QValue StringNumberIntersection
stringNumberIntersection = QIntersectionThere stringIntersection


-- functions
Number2Func : QType QTFFunction
Number2Func = QTFunction QTNumber QTNumber

Number3Func : QType QTFFunction
Number3Func = QTFunction QTNumber Number2Func

addNum : QValue Number2Func
addNum = QFunction (\ (QNumber n) => let QNumber num' = num in (QNumber (n + num')))

addNums : QValue Number3Func
addNums = QFunction (\ (QNumber m) => QFunction (\ (QNumber n) => (QNumber (m + n))))


-- expressions
two : QExpression QTNumber
two = QNeutral (QNumber 2)

three : QExpression QTNumber
three = QLambda (QNumber 1) (QNeutral addNum)

four : QExpression QTNumber
four = QLambda num (QLambda num (QNeutral addNums))
