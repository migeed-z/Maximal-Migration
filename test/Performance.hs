import Criterion.Main
import Examples
import SolveEq
import Algorithms
import Lang
import Maximality
import NPHard
import Formula


make_benchmark expr num f = bench (show num)  $ nf (f expr) tenv


-- Our benchmark harness.
main = defaultMain [
  bgroup "Singleton " [
                (make_benchmark (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))) 1 ismaximal)
               ,(make_benchmark succ_lam_true 2 ismaximal)
               ,(make_benchmark my_lam 3 ismaximal)
               ,(make_benchmark simple_app 4 ismaximal)
               ,(make_benchmark (App (Vv "succ") (App(Lam Tdyn "y" (Vv "y"))
                (App (Lam Tdyn "x" (Vv "x"))(Vb True)))) 5 ismaximal)
               ,(make_benchmark (Lam Tdyn "x" (Vv "x")) 6 ismaximal)
               ,(make_benchmark lam_xyy 7 ismaximal)
               ,(make_benchmark evil 8 ismaximal)
               ,(make_benchmark evil_example 9 ismaximal)
               ,(make_benchmark self_application 10 ismaximal)
               ,(make_benchmark lam_term_1 11 ismaximal)
               ,(make_benchmark app_term_2 12 ismaximal)
               ],



  bgroup "Finiteness " [
                (make_benchmark (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))) 1 check_finitness)
               ,(make_benchmark succ_lam_true 2 check_finitness)
               ,(make_benchmark my_lam 3 check_finitness)
               ,(make_benchmark simple_app 4 check_finitness)
               ,(make_benchmark (App (Vv "succ") (App(Lam Tdyn "y" (Vv "y"))
                (App (Lam Tdyn "x" (Vv "x"))(Vb True)))) 5 check_finitness)
               ,(make_benchmark (Lam Tdyn "x" (Vv "x")) 6 check_finitness)
               ,(make_benchmark lam_xyy 7 check_finitness)
               ,(make_benchmark evil 8 check_finitness)
               ,(make_benchmark self_application 9 check_finitness)
               ],


  bgroup "FLarge " [
                (make_benchmark  evil_example 10 check_finitness)
               ,(make_benchmark  lam_term_1 11 check_finitness)
               ,(make_benchmark app_term_2 12 check_finitness)
               ],

  bgroup "TopChoice " [ 
                (make_benchmark (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))) 1 topchoice)
               ,(make_benchmark succ_lam_true 2 topchoice)
               ,(make_benchmark my_lam 3 topchoice)
               ,(make_benchmark simple_app 4 topchoice)
               ,(make_benchmark (App (Vv "succ") (App(Lam Tdyn "y" (Vv "y"))
                (App (Lam Tdyn "x" (Vv "x"))(Vb True)))) 5 topchoice)
               ,(make_benchmark (Lam Tdyn "x" (Vv "x")) 6 topchoice)
               ,(make_benchmark lam_xyy 7 topchoice)
               ,(make_benchmark evil 8 topchoice)
               ,(make_benchmark self_application 9 topchoice)
               ],

  bgroup "TCLarge " [ 
               (make_benchmark evil_example 10 topchoice)
               ,(make_benchmark lam_term_1 11 topchoice)
               ,(make_benchmark app_term_2 12 topchoice)
               ],


  bgroup "Maximality " [
                (make_benchmark (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))) 1 closestMaximalMigration_5)
               ,(make_benchmark succ_lam_true 2 closestMaximalMigration_5)
               ,(make_benchmark my_lam 3 closestMaximalMigration_5)
               ,(make_benchmark simple_app 4 closestMaximalMigration_5)
               ,(make_benchmark (App (Vv "succ") (App(Lam Tdyn "y" (Vv "y"))
                (App (Lam Tdyn "x" (Vv "x"))(Vb True)))) 5 closestMaximalMigration_5)
               ,(make_benchmark (Lam Tdyn "x" (Vv "x")) 6 closestMaximalMigration_5)
               ,(make_benchmark lam_xyy 7 closestMaximalMigration_5)
               ,(make_benchmark evil 8 closestMaximalMigration_5)
               ,(make_benchmark self_application 9 closestMaximalMigration_5)

               ],


  bgroup "MLarge" [
                (make_benchmark evil_example 10 closestMaximalMigration_5)
               ,(make_benchmark lam_term_1 11 closestMaximalMigration_4)
               ,(make_benchmark app_term_2 12 closestMaximalMigration_4)
               ],


  bgroup "MappingSAT " [
                (make_benchmark (make_mapping fpaper) 13 closestMaximalMigration_4)
               ],


  bgroup "MappingUNSAT " [
                (make_benchmark (make_mapping f8) 14 closestMaximalMigration_3)
               ]

  ]


    -- example lam_xx_plus_xx Nothing
    -- example final (Just max_final)
    -- example my_lam (Just my_lam_max)
    -- example simple_app (Just simple_app_max)
    -- example lam_xyy (Just lam_xyy_max)
    -- example evil_example (Just evil_example_max)
    -- example (Lam Tdyn "x" (Vv "x")) (Just (Lam Tint "x" (Vv "x")))
    -- example self_application Nothing
    -- example succ_lam_true (Just succ_lam_true_max)
    -- example evil (Just evil_m)
    -- example (Lam Tdyn "x" (App (Vv "x") my_succ))  (Just (Lam (Tdyn ~> Tint) "x" (App (Vv "x") my_succ)))
    -- example (App (Vv "succ") 
    --         (App(Lam Tdyn "y" (Vv "y"))
    --             (App (Lam Tdyn "x" (Vv "x"))(Vb True)))) (Just (App (Vv "succ") 
    --         (App(Lam Tint "y" (Vv "y"))
    --             (App (Lam Tdyn "x" (Vv "x"))(Vb True)))))

    -- example (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))) (Just (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))))
    -- example (App (Lam Tint "x" (Vv "x")) (Vb True)) Nothing