{-# LANGUAGE OverloadedStrings #-}
module Algorithms where

import Data.List as List
import Control.Monad
import TypeCheck
import Lang
import Constraint

import NPHard

import Formula



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

match :: Constraint -> [(Int, [Constraint])]
match (Matching (CVar v)(CArr (CVar v1)(CVar v2))) = 
  [ (1, [ (CVar v) .=  ((CVar v1) .~> (CVar v2)) ])
  , (2, [ (CVar v) .= CDyn
        , (CVar v1) .= CDyn
        , (CVar v2) .= CDyn
        ]
    )
  ] 
match x = 
  [(0, [x])]

simMatch :: [Constraint] -> [[Constraint]]
simMatch cs = map concat . sequence $ 
  [ map snd (match c)
  | c <- cs
  ]

simMatch' :: [Constraint] -> [([Int], [Constraint])]
simMatch' cs = map fn . sequence $ 
  [ match c
  | c <- cs
  ]
  where
    fn :: [(Int, [Constraint])] -> ([Int], [Constraint])
    fn ls = (map fst ls, concatMap snd ls)

  
--call our constraints simplifier till we get a fixed point
fixed :: Eq a => (a -> a) -> a -> a
fixed f a 
  | a == a' = a
  | otherwise = fixed f a'
  where a' = f a


-- printProgress :: Expr -> IO ()
-- printProgress expr =

--   forM_ (compose_upto_match expr tenv) $ \(i, s) -> do
--       print (filter (/=0) i)

--   where
--     -- Compose all operations
--     compose_upto_match :: Expr -> Env -> [([Int],[Constraint])]
--     compose_upto_match expr env = (simMatch' (snd (fixed simPrec (constraint expr env))))

-- main2 = do
--   let f1 = [Cl (Neg "x0") (Neg "x1") (Neg "x2")]
--   printProgress (make_mapping f1)
