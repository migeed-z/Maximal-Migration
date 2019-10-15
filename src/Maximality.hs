{-# Language ViewPatterns #-}
{-# Language LambdaCase #-}

module Maximality where
import Control.Monad (guard)
import Data.Maybe (isJust)
import Lang
import TypeCheck
import Data.Monoid (First (..), mconcat)
import Data.Maybe
import Counting
import qualified Data.Set as Set
import SolveEq


unique :: Eq a => [a] -> [a]
unique []       = []
unique (x : xs) = x : unique (filter (x /=) xs)


first :: [Maybe a] -> Maybe a
first = getFirst . mconcat . map First

findWellTypedMigrationsAtDepth :: Int -> Expr -> Env -> [Expr]
findWellTypedMigrationsAtDepth n t env
  | not $ type_checks t env = 
    []
  | n > 0 = 
    concat 
    [ findWellTypedMigrationsAtDepth (n-1) s env 
    | s <- get_the_next_term t 
    ]
  | otherwise = 
    [ t ]

      

-- finds ALL maximal migration in exactly depth N, if they exists.
findMaximalMigrationsAtDepth :: Int -> Expr -> Env -> [Expr]
findMaximalMigrationsAtDepth n t env =
   [ t' | t' <- findWellTypedMigrationsAtDepth n t env, ismaximal t' env]



-- Returns the maximals upto level n
findAllMaximalMigrationsN :: Int -> Expr -> Env -> [Expr]
findAllMaximalMigrationsN d t env =
  concat [ findMaximalMigrationsAtDepth n t env | n <- [0..d+1]]

-- Returns all maximal migrations
findAllMaximalMigrations :: Expr -> Env -> [Expr]
findAllMaximalMigrations t env =
  concat [ findMaximalMigrationsAtDepth n t env | n <- [0..]]
  -- where
  --   maximalNumberOfSteps = 
  --     (migration_limit t env)  * (count_types t)


-- Returns the maximal migration closest to the term.
-- used only when the lattice is finite
findAllMaximalMigrationsUnlimited :: Expr -> Env -> [Expr]
findAllMaximalMigrationsUnlimited t env =
  concat 
  . map (unique . filter (\t' -> ismaximal t' env))
  . takeWhile (not . null)
  $ [ findWellTypedMigrationsAtDepth n t env | n <- [0..]]

-- | finds the maximal migration in exactly depth N, if it exists.
findMaximalMigration :: Int -> Expr -> Env -> Maybe Expr
findMaximalMigration n t env =
  case findMaximalMigrationsAtDepth n t env of
    x:_ -> Just x
    [] -> Nothing




-- Returns the semi algorithm for maximal migraiton.
closestMaximalMigration :: Expr -> Env -> Maybe Expr
closestMaximalMigration t env =
    case findAllMaximalMigrations t env of
    x:_ -> Just x
    [] -> Nothing

-- Returns the first maximal migration
-- stops at level n
closestMaximalMigration_n :: Expr -> Int ->  Env -> Maybe Expr
closestMaximalMigration_n t n env =
    case findAllMaximalMigrationsN n t env of
    x:_ -> Just x
    [] -> Nothing


--Hardcoded version with particular levels for performance
closestMaximalMigration_3 :: Expr -> Env -> Maybe Expr
closestMaximalMigration_3 t env =
    case findAllMaximalMigrations_3 t env of
    x:_ -> Just x
    [] -> Nothing

closestMaximalMigration_4 :: Expr -> Env -> Maybe Expr
closestMaximalMigration_4 t env =
    case findAllMaximalMigrations_4 t env of
    x:_ -> Just x
    [] -> Nothing


closestMaximalMigration_5 :: Expr -> Env -> Maybe Expr
closestMaximalMigration_5 t env =
    case findAllMaximalMigrations_5 t env of
    x:_ -> Just x
    [] -> Nothing



findAllMaximalMigrations_3 e env = (findAllMaximalMigrationsN 3 e env)

findAllMaximalMigrations_4 e env = (findAllMaximalMigrationsN 4 e env)

findAllMaximalMigrations_5 e env = (findAllMaximalMigrationsN 5 e env)


--Finds all top choices if they exist
topchoice :: Expr -> Env -> [Expr]
topchoice e env = 
  case (check_finitness e env) of 
    True -> (findAllMaximalMigrationsUnlimited e env)
    otherwise -> []

--Another variation of the semi algorithm which checks for finitness first
finalMaximalMigration :: Expr -> Env -> [Expr]
finalMaximalMigration e env = 
  case (check_finitness e env) of 
    True -> (findAllMaximalMigrationsUnlimited e env)
    otherwise -> (findAllMaximalMigrations e env)

--for a given level in the lattice, check if anything is maximal
is_any_term_maximal :: [Expr] -> Env -> Maybe Expr
is_any_term_maximal [] _ = Nothing
is_any_term_maximal (x:xs) env = case (ismaximal x env) of
    True -> Just x
    False -> (is_any_term_maximal xs env)

--is this current migration maximal?
ismaximal :: Expr -> Env -> Bool
ismaximal e env =  (null (get_the_next_well_typed_term e env))


--does this term type-check?
type_checks :: Expr -> Env -> Bool
type_checks e env = 
    case (typecheck e env) of
          Just t -> True
          otherwise -> False

--get the next more precise types (one level up the lattice)
get_the_next_type :: Vtype -> [Vtype]
get_the_next_type Tdyn = [(Tdyn ~> Tdyn), Tint, Tbool]
get_the_next_type (Tfun t1 t2) = 
     [(Tfun s1 t2) | s1 <- (get_the_next_type t1)] ++
     [(Tfun t1 s2) | s2 <- (get_the_next_type t2)] 
get_the_next_type Tint = []
get_the_next_type Tbool = []


--get the better term one level up the lattice
get_the_next_term :: Expr -> [Expr]
get_the_next_term (Lam typ x e) = 
    [(Lam s x e) | s <- (get_the_next_type typ)] ++
    [(Lam typ x e') | e' <- (get_the_next_term e)]

get_the_next_term (App e1 e2) = 
    [(App e1' e2) | e1' <- (get_the_next_term e1)] ++
    [(App e1 e2') | e2' <- (get_the_next_term e2)]
get_the_next_term _ = []

get_the_next_well_typed_term :: Expr -> Env -> [Expr]
get_the_next_well_typed_term e env = 
    [trm | trm <- (get_the_next_term e), (type_checks trm env)]


type_test_succ = do
  let app_y = (Lam (Tdyn ~> Tdyn) "y" (Vv "x"))
  let app_x = (App app_y (Vv "x"))
  let app_xx = (App app_x (Vv "x"))
  let lam = (Lam Tdyn "x" app_xx)
  print(get_the_next_well_typed_term lam tenv)


-- test_printer = do
--   -- let app_5 = (App (Lam Tdyn "x" (Vv "x")) (Vi 5))

--   -- let app_f_5 = (App (Vv "f") app_5)

--   -- let lam_z = (Lam Tdyn "z"  app_f_5 )

--   -- let app_f_true = (App (Vv "f") (Vb True))

--   -- let lam_f = (Lam Tdyn "f" (App lam_z app_f_true))

--   -- let lam_y = (Lam Tdyn "y" (Vv "y"))

--   -- let my_app = (App  lam_f lam_y)



--   let my_succ = (App (Vv "succ") (App (Lam Tdyn "y" (Vv "y")) 
--                 (App (Lam Tdyn "x" (Vv "x")) (Vb True)) ) )


--   print(my_succ)
--   print(findWellTypedMigrations my_succ tenv)
--   -- print(closestMaximalMigration my_app tenv)



