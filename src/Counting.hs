--We want to determine the maximum size of the type
--For it to have a maximal migration.
--After that point, the program cannot have a maximal migration.
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
  --  (match_on_var x typ term ((x,typ):env)) + (migration_limit term ((x,typ):env))
migration_limit (App e1 e2) env = (migration_limit e1 env) + (migration_limit e2 env) + 1

-- λx : * -> int . (λy : int . (λz : int . True) (succ (x True))) (succ (x 4))

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



-- count_apps_abs :: Expr -> Int
-- count_apps_abs (Vi n) = 0
-- count_apps_abs (Vb b) = 0
-- count_apps_abs (Vv x) = 0
-- count_apps_abs 

-- type_test_succ = do
--     let identity = (Lam Tdyn "x" (Vv "x"))
--     let x_4 = (App (Vv "x") (Vi 4))
--     let x_true = (App (Vv "x") (Vb True))
--     let my_succ = (App (Vv "succ") x_true)
--     let my_succ2 = (App (Vv "succ") x_4)
--     let lam_z = (Lam Tint "z" (Vb True))
--     let first_app = (App lam_z my_succ)
--     let lam_y = (Lam Tint "y" first_app)
--     let appx  = (App lam_y my_succ2)
--     let final = (Lam (Tdyn ~> Tint) "x" appx)

--     print(match_on_var "x" x_true (("x",Tdyn ~> Tint):tenv))









--     print(typ_precision Tdyn Tdyn)
--     print(typ_precision Tdyn (Tint ~> Tint))
--     print(typ_precision (Tint ~> Tint) Tdyn)


