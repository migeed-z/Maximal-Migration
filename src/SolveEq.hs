{-# Language DeriveFoldable #-}
{-# Language DeriveFunctor #-}
{-# Language DeriveDataTypeable #-}
{-# Language MultiParamTypeClasses #-}
{-# Language DeriveTraversable #-}
{-# Language LambdaCase #-}
{-# Language FlexibleContexts #-}
{-# Language TypeOperators #-}
{-# Language TemplateHaskell #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
{-# Language ViewPatterns #-}


--capture avoidance not accounted for in this solver
module SolveEq where
import Data.Data
import Data.List as List
import Data.Comp.Variables
import Data.Comp.Unification
import Data.Comp.Term
import Data.Comp.Derive
import Constraint
import Data.Bool(bool)
import Control.Monad(liftM2)
-- import Data.Void
-- import Data.List as List
-- import Data.Set as Set
-- import Data.Foldable as Foldable
import Data.Maybe (fromJust)
import Data.Maybe (isJust)
-- import Data.Maybe (isJust)
-- import TypeCheck
-- import Data.Typeable
-- import Lang
-- import Algorithms
import qualified Data.Map as Map
import Lang
import Algorithms


-- main :: IO ()    -- This says that main is an IO action.
-- main = return () -- This tells main to do nothing.

data CTypeF a 
    = CVarF Int 
    | CArrF a a
    | CIntF
    | CDynF
    | CBoolF
    deriving (Data, Functor, Foldable, Traversable, Show, Eq)

$(makeShowF ''CTypeF)


instance HasVars CTypeF Int where
    isVar (CVarF x) = Just x
    isVar (CArrF x y) = Nothing
    isVar CIntF = Nothing
    isVar CBoolF = Nothing
    isVar CDynF = Nothing

type CType_ = Term CTypeF

ctypeTof :: CType -> CType_
ctypeTof CInt = Term CIntF
ctypeTof CBool = Term CBoolF
ctypeTof CDyn = Term CDynF
ctypeTof (CVar i) = Term (CVarF i)
ctypeTof (CArr a b) = Term (CArrF (ctypeTof a) (ctypeTof b))


toFequations :: [Constraint] -> (Equations CTypeF)
toFequations [] = []
toFequations ((Equality a b) : xs) = ((ctypeTof a), (ctypeTof b)) : (toFequations xs)
toFequations (x : xs) = (toFequations xs) 

unravel :: CType_ -> CType
unravel a = 
    case unTerm a of 
        CVarF i -> CVar i
        CArrF a b -> CArr (unravel a) (unravel b)
        CIntF -> CInt
        CBoolF -> CBool
        CDynF -> CDyn 

--calls the unification algorithm on the equality
call_unifier :: [Constraint] -> Either (UnifError CTypeF Int) (Subst CTypeF Int)
call_unifier c = (unify (toFequations c))

pleaseUnify :: [Constraint] -> Either String [(Int, CType)]
pleaseUnify cnt = case (call_unifier cnt) of
  Left (FailedOccursCheck v term) -> 
    Left ("failed occurs check " ++ show v ++ ": " ++ (show $ unravel term))
  Left (HeadSymbolMismatch t1 t2) -> 
    Left ("head symbol mismatch " ++ show (unravel t1)  ++ " =/= " ++ (show $ unravel t2))
  Left (UnifError str) -> 
    Left str
  Right (subst :: Subst CTypeF Int) -> 
    Right (Map.toList $ fmap unravel subst)


--apply unifier to consistency constraints
getConsistConst :: [Constraint] -> [Constraint]
getConsistConst [] = []
getConsistConst (Consistency c1 c2 :xs) = 
    (Consistency c1 c2) : (getConsistConst xs)
getConsistConst (x:xs) = (getConsistConst xs)


--substitute type in solution
substituteSol :: CType -> [(Int, CType)] -> CType

substituteSol (CVar x) (List.lookup x -> Just t) = t
substituteSol (CArr v1 v2) sol = (CArr (substituteSol v1 sol)  
                                       (substituteSol v2 sol))
substituteSol t sol = t

--does this need to be applied till a fixed point?
apply_unifier ::  [Constraint] -> [(Int, CType)] -> [Constraint]
apply_unifier  [] sol = []
apply_unifier ((Consistency v1 v2):xs) sol = (Consistency (substituteSol v1 sol) 
                                                    (substituteSol v2 sol)) :
                                        (apply_unifier xs sol)
apply_unifier (x:xs) sol = (apply_unifier xs sol)

fixed_uni :: Eq a => (a -> b -> a) -> a -> b -> a
fixed_uni f a b
  | a == a' = a
  | otherwise = fixed_uni f a' b
  where a' = f a b


simConSing:: Constraint -> Maybe [Constraint]
simConSing (Consistency (CArr t1 t2) CBool) = Nothing
simConSing (Consistency (CArr t1 t2) CInt) = Nothing
simConSing (Consistency CBool (CArr t1 t2)) = Nothing
simConSing (Consistency CInt (CArr t1 t2)) = Nothing
simConSing (Consistency CBool CInt) = Nothing
simConSing (Consistency CInt CBool) = Nothing
simConSing (Consistency CBool CBool) = Just []
simConSing (Consistency CInt CInt) = Just []
simConSing (Consistency t CDyn) = Just []
simConSing (Consistency CDyn t) = Just []
simConSing (Consistency (CArr t1 t2) (CArr t1' t2')) = 
                        Just [(Consistency t1 t1'),
                              (Consistency t2 t2')]
simConSing (Consistency (CVar v1) (CVar v2)) = Just [(Consistency (CVar v1) (CVar v2))]
simConSing (Consistency t (CVar v)) = Just [(Consistency (CVar v) t)]
simConSing c = Just [c]

simCon :: [Constraint] -> Maybe [Constraint]
simCon [] = Just []
simCon (x:xs) = case ((simConSing x), (simCon xs))  of
              (Nothing, _) -> Nothing
              (_, Nothing) -> Nothing
              (Just lst, _) -> Just (lst ++ (concat (simCon xs)))

--fixed point for simCon
fixedM :: (Eq a, Monad m) => (a -> m a) -> a -> m a
fixedM f = go
    where go x = f x >>= liftM2 bool go pure <*> (x ==)

--compose all upto simCon
compose_all :: Expr -> Env -> [Maybe [Constraint]]
compose_all expr env = [fixedM simCon c | c <-(apply_unifier_to_2n (compose_upto_match expr env))]

--compose 2n and remove the ones with no solution.
apply_unifier_to_2n :: [[Constraint]] -> [[Constraint]]
apply_unifier_to_2n [] = []
apply_unifier_to_2n (x:xs) = case (pleaseUnify x) of 
          (Left _) -> (apply_unifier_to_2n xs)
          (Right sol) -> ((apply_unifier x sol) : (apply_unifier_to_2n xs))

-- Compose all operations
compose_upto_match :: Expr -> Env -> [[Constraint]]
compose_upto_match expr env = (simMatch (snd (fixed simPrec (constraint expr env))))

-- Boundedness
filter_isjust :: [Maybe [Constraint]] -> [[Constraint]]
filter_isjust lst = [(fromJust x) | x <- lst, (isJust x)]
  

--is leaf (expecting no dyn in the type)
hasStaticLeaf :: CType -> Bool
hasStaticLeaf CInt = True
hasStaticLeaf CBool = True
hasStaticLeaf (CArr t1 t2) = (hasStaticLeaf t1) && 
                             (hasStaticLeaf t2)
hasStaticLeaf _ = False


-- check boundedness
-- 0 = left
-- 1 = right
-- 2 = both
boundnessOneVar :: CType -> [Constraint] -> Int -> Bool
boundnessOneVar (CVar v) [] direc = False
boundnessOneVar (CVar v1) ((Consistency (CVar v2) CInt) :xs) direc | v1 == v2 = True 
boundnessOneVar (CVar v1) ((Consistency (CVar v2) CBool):xs) direc | v1 == v2 = True

boundnessOneVar (CVar v1) ((Consistency (CVar v2) (CArr t1 t2)):xs) 2 | v1 == v2 = 
  case ((hasStaticLeaf t1),(hasStaticLeaf t2)) of 
    (True, True) -> True
    (True, False) -> (boundnessOneVar (CVar v1)  xs 1)
    (False, True) -> (boundnessOneVar (CVar v1)  xs 0)
    (False, False) -> (boundnessOneVar (CVar v1)  xs 2)


boundnessOneVar (CVar v1) ((Consistency (CVar v2) (CArr t1 t2)):xs) 1 | v1 == v2 = 
  case ((hasStaticLeaf t1),(hasStaticLeaf t2)) of 
    (_, True) -> True
    otherwise -> (boundnessOneVar (CVar v1)  xs 1)

boundnessOneVar (CVar v1) ((Consistency (CVar v2) (CArr t1 t2)):xs) 0 | v1 == v2 = 
  case ((hasStaticLeaf t1),(hasStaticLeaf t2)) of 
    (True, _) -> True
    otherwise -> (boundnessOneVar (CVar v1)  xs 0)

boundnessOneVar (CVar v) (x:xs) direc = (boundnessOneVar (CVar v) xs direc) 


boundnessOneSet :: [Constraint] -> [Constraint] -> Bool
boundnessOneSet [] _ = True --might need to turn this into False
boundnessOneSet ((Consistency (CVar v) c) : xs) lst = (boundnessOneVar (CVar v) lst 2) &&
                                                      (boundnessOneSet xs lst)

boundedness :: [[Constraint]] -> Bool
boundedness cnst = not (elem False 
                       [(boundnessOneSet cnst_set cnst_set) | 
                        cnst_set <- cnst])


check_finitness :: Expr -> Env -> Bool
check_finitness e env = (boundedness (filter_isjust (compose_all e env)))










