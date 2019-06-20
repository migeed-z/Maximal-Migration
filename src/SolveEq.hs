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
-- import Data.Void
-- import Data.List as List
-- import Data.Set as Set
-- import Data.Foldable as Foldable
import Data.Maybe (fromJust)
-- import Data.Maybe (isJust)
-- import TypeCheck
-- import Data.Typeable
-- import Lang
-- import Algorithms
import qualified Data.Map as Map


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

-- (CVar x) sol =  fromJust (List.lookup x sol)
-- substituteSol CInt sol = CInt
-- substituteSol CBool sol = CBool
-- substituteSol CDyn sol = CDyn

apply_unifier ::  [Constraint] -> [(Int, CType)] -> [Constraint]
apply_unifier  [] sol = []
apply_unifier ((Consistency v1 v2):xs) sol = (Consistency (substituteSol v1 sol) 
                                                    (substituteSol v2 sol)) :
                                        (apply_unifier xs sol)
apply_unifier (x:xs) sol = (apply_unifier xs sol)


--fixed point todo





