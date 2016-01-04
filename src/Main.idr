import Q

import Data.HVect
import Data.Vect


-- -- strings
-- str : QValue QTString
-- str = QString "aoeu"

-- -- numbers
-- num : QValue QTNumber
-- num = QNumber 2


-- -- unions
-- StringUnion : QType QTFUnion
-- StringUnion = QTUnion QTString QTEmptyUnion

-- StringNumberUnion : QType QTFUnion
-- StringNumberUnion = (QTUnion QTNumber StringUnion)

-- emptyUnion : QValue QTEmptyUnion
-- emptyUnion = QEmptyUnion

-- stringUnion : QValue StringUnion
-- stringUnion = QUnion str emptyUnion

-- stringNumberUnion : QValue StringNumberUnion
-- stringNumberUnion = QUnion num (QUnion str emptyUnion)


-- -- intersections
-- StringIntersection : QType QTFIntersection
-- StringIntersection = QTIntersection QTString QTEmptyIntersection

-- StringNumberIntersection : QType QTFIntersection
-- StringNumberIntersection = QTIntersection QTNumber StringIntersection

-- emptyIntersection : QValue QTEmptyIntersection
-- emptyIntersection = QEmptyIntersection

-- stringIntersection : QValue StringIntersection
-- stringIntersection = QIntersectionHere str QEmptyIntersection

-- stringNumberIntersection : QValue StringNumberIntersection
-- stringNumberIntersection = QIntersectionThere stringIntersection


-- -- functions
-- Number2Func : QType QTFFunction
-- Number2Func = QTFunction QTNumber QTNumber

-- Number3Func : QType QTFFunction
-- Number3Func = QTFunction QTNumber Number2Func

-- addNum : QValue Number2Func
-- addNum = QFunction (\ (QNumber n) => let QNumber num' = num in (QNumber (n + num')))

-- addNums : QValue Number3Func
-- addNums = QFunction (\ (QNumber m) => QFunction (\ (QNumber n) => (QNumber (m + n))))


-- -- expressions
-- two : QExpression QTNumber
-- two = QNeutral (QNumber 2)

-- three : QExpression QTNumber
-- three = QLambda (QNumber 1) (QNeutral addNum)

-- four : QExpression QTNumber
-- four = QLambda num (QLambda num (QNeutral addNums))


-- aToA : QType QTFTypeFunction
-- aToA = QTTypeFunction id id


-- listIntersection : QType a -> QType QTFIntersection
-- listIntersection {a} t = qIntersection {flags=[QTFNull, a]} [QTNull, t]


-- qList : QType QTFTypeFunction
-- qList = QTTypeFunction (\_ => QTFIntersection) (\t => listIntersection t)


-- qMap : QType QTFTypeFunction
-- qMap = QTTypeFunction (\_ => QTFFunction) (\t => )


main : IO ()
main = return ()


{-

look out for

exists:
A -> B -> C -> D

searching for:
a -> C -> D

we want to find that function!

(and we will!  a will bind to B; A will be one of those free variables
that the user must fill in.  so it will work.)

-}


{-

look out for

exists:
(a -> b -> c) -> d -> a -> b -> c

searching for:
(a -> b) -> a -> b

-}
