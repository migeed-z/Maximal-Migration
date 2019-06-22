module Algorithms where

import Data.List as List
import Control.Monad
import TypeCheck
import Lang
import Constraint



isCType :: CType -> Bool
isCType CInt = True
isCType CDyn = True
isCType CBool = True
isCType (CArr t1 t2) = (isCType t1) && (isCType t2)
isCType _ = False


extract_num :: CType -> Int
extract_num (CVar n) = n


simPrec_sing :: (CType, Constraint) -> (CType, [Constraint])
simPrec_sing (ctyp, cons) = snd $ runState (go (ctyp, cons)) (extract_num ctyp + 1) where
  go ::  (CType, Constraint) -> State Int (CType, [Constraint])

  go (ctyp, cons) = do 
   case cons of
      (Precision CDyn (CVar n)) -> do
        return (ctyp, [])  

      (Precision CBool (CVar n)) -> do
        return (ctyp, [(CVar n) .= CBool])
     
      (Precision CInt (CVar n)) -> do 
        return (ctyp, [(CVar n) .= CInt])

      (Precision (CArr t1 t2) (CVar v))  -> do 
        v1 <- gen
        v2 <- gen
        return (v2, [(CVar v) .= (v1 .~> v2), (t1 .<= v1), (t2 .<= v2)])

      c -> do
        return (ctyp, [c])
              -- where (isCType t1 && isCType t2)

--step 1: simPrec
simPrec :: (CType, [Constraint]) ->  (CType, [Constraint])
simPrec (typ, []) = (typ, [])
simPrec (typ, x:xs) = ((fst rstc),(snd fstc) ++ (snd rstc))
    where fstc = (simPrec_sing (typ, x))
          rstc = (simPrec ((fst fstc), xs))

--step 2
--first possibility
simMatch_sing1 :: Constraint -> [Constraint]
simMatch_sing1 (Matching (CVar v)(CArr (CVar v1)(CVar v2))) = 
  [(CVar v) .=  ((CVar v1) .~> (CVar v2))] 


--second possibility
simMatch_sing2 :: Constraint ->  [Constraint]
simMatch_sing2 (Matching (CVar v)(CArr (CVar v1)(CVar v2)))  = 
  [(CVar v) .= CDyn, (CVar v1) .= CDyn, (CVar v2) .= CDyn]


applicable_s :: Constraint -> Bool
applicable_s (Matching (CVar v)(CArr (CVar v1)(CVar v2))) = True
applicable_s _ = False

simMatch :: [Constraint] -> [[Constraint]]
simMatch cs = map concat . sequence $
    [ concat $ [ [ [c]   | not (applicable_s c)]
               , [ simMatch_sing1 c  | applicable_s c]
               , [ simMatch_sing2 c  | applicable_s c] ]
      | c <- cs]

             
-- --add non-applicable elements to every sublist
-- process_combinations :: [[Constraint]] -> [Constraint] -> [[Constraint]]
-- process_combinations (x:xs) cnst = (x  ++ (filter (not . applicable_s) cnst)) : 
--                                    (process_combinations xs cnst)
-- process_combinations [] _ = []


-- simMatch :: [Constraint] -> [[Constraint]]
-- simMatch const = (process_combinations (combinations (filter applicable_s const)) const)

--call our constraints simplifier till we get a fixed point
fixed :: Eq a => (a -> a) -> a -> a
fixed f a 
  | a == a' = a
  | otherwise = fixed f a'
  where a' = f a


my_test = do
    -- let c0 = CVar 4 .=  CBool

    let c1 = CVar 0 .=  CInt
    let c2 = (CVar 3) .|> (CArr (CVar 1)(CVar 2))
    let c3 = (CVar 6) .|> (CArr (CVar 7)(CVar 8))
    let c4 = (CVar 10) .|> (CArr (CVar 11)(CVar 12))
    -- let comb = combinations [c2, c3]
    -- let prossess = (process_combinations comb [c0, c1])
    -- let finals = (simMatch [c0, c1, c2, c3])
    print([c1,c2,c3,c4])
    -- print(simMatch_sing1 c2)
    -- print(simMatch_sing2 c2)
    print(simMatch [c1, c2, c3, c4])
