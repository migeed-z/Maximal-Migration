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

--capture avoidance not accounted for in this solver
module SolveEq where
import Data.Typeable
import Data.Data
import Data.Void
import Data.List as List
import Data.Map as Map
import Data.Set as Set
import Data.Foldable as Foldable
import Data.Maybe (fromJust)
import Data.Maybe (isJust)
import Control.Monad
import TypeCheck
import Data.Comp.Variables
import Data.Comp.Unification
import Data.Comp.Term
import Data.Comp.Derive
import Constraint
import Lang
import Algorithms


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

-- getUnificationResults :: Either (UnifError CTypeF Int) (Subst CTypeF Int) -> (Subst CTypeF Int)
-- getUnificationResults res = case res of
--   Left (FailedOccursCheck v term) -> Nothing
--   Left (HeadSymbolMismatch t1 t2) -> Nothing
--   Left (UnifError str)              -> Nothing
--   Right (subst :: Subst CTypeF Int) -> (Just (fmap unravel subst))

-- By matching against Left and Right, we're letting GHC know that unify
-- should return an Either; this disambiguates `m`


-- cnst = (constraint lam_xx tenv)
-- cnst_simprec = (simPrec cnst)
-- cnst_simMatch = (simMatch (snd cnst_simprec))
-- cnst_simMatch1 = (head cnst_simMatch)
-- cnst_simMatch2 = (last cnst_simMatch)
-- cnst_test = [CVar 0 .= (CVar 1 .~> CVar 2), 
--             (CVar 3) .= (CVar 5 .~> CVar 2),
--              CVar 3 .= CVar 1,
--              CVar 4 .= CVar 1]

-- c0 = Term (CVarF 0)
-- c1 = Term (CVarF 1)
-- c2 = Term (CVarF 2)
-- c3 = Term (CVarF 3)
-- c4 = Term (CVarF 4)
-- c5 = Term (CVarF 5)

-- eq1 = (c0, (Term (CArrF c1 c2)))
-- eq2 = (c3, (Term (CArrF c5 c2)))
-- eq3 = (c3, c1)
-- eq4 = (c4, c1)

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




-- main = case (call_unifier cnst_simMatch1) of
--   Left (FailedOccursCheck v term) -> putStrLn ("failed occurs check " ++ 
--                                      show v ++ ": " ++ (show $ unravel term))
--   Left (HeadSymbolMismatch t1 t2) -> putStrLn ("head symbol mismatch " ++ 
--                                      show (unravel t1)  ++ " =/= " ++ 
--                                      (show $ unravel t2))
--   Left (UnifError str)              -> putStrLn str
--   Right (subst :: Subst CTypeF Int) -> print (fmap unravel subst)





