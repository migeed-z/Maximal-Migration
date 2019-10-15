--experimental
--We want to determine the maximum size of the type
--For it to have a maximal migration.
{-# Language ViewPatterns #-}


module Counting where
import Lang
import TypeCheck
import Data.Maybe (fromJust)

--calculates the cardinality of a given type
card :: Vtype -> Int
card Tint = 0
card Tbool = 0
card Tdyn = 0
card (Tfun t1 t2) = 1 + (card t1) + (card t2) 


--calculates the number of type annotations in an expression
count_types :: Expr -> Int
count_types (Lam typ var expr) = 1 + (count_types expr)
count_types (App t1 t2) = (count_types t1) + (count_types t2)
count_types _ = 0


-- ASSUME WELL TYPED TERM UNDER ENV
--compute maximal migration cardinality limit for a closed program
migration_limit :: Expr -> Env -> Int
migration_limit (Vi n) _ = 0
migration_limit (Vb b) _ = 0
migration_limit (Vv x) (envlookup x -> Just t) = (card t)
migration_limit (Lam typ x term) env = migration_limit term ((x,typ):env)
migration_limit (App e1 e2) env = (migration_limit e1 env) + (migration_limit e2 env) + 1


--note that you may want to look at all applications in general
match_on_var :: Name -> Vtype -> Expr -> Env -> Int
match_on_var x typeofx term env =
    case term of 
        App (Vv x2) e
            | x == x2 ->  
                card typeofx + 1 + (match_on_var x typeofx e env)    --function, so add 1, plus anymore uses on x + |x|

        (App e1 e2) ->
            (match_on_var x typeofx e1 env) + (match_on_var x typeofx e2 env)

        Lam typ x2 term  ->  (match_on_var x typeofx term env)  --assume x did not get erased so proceed to the body of the function
        
        term -> card typeofx  --x did not occur in the body so just take the type environment since we know it type-checks. 




