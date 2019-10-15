{-# Language QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Hspec
import Examples
import Data.List
import Maximality
import TypeCheck
import Counting
import Lang
import TH
import Constraint
import Algorithms
import SolveEq
import Data.Either
import NPHard
import Formula
import Data.Maybe 
import qualified Data.Map as Map

main :: IO ()
main = test

test :: IO ()
test = hspec $ do
    test_maximality
    test_topchoice
    test_finitness
    test_has_max
    test_has_max_large
    test_migrate_semi
    test_migrate
    test_migrate_large
    test_lam_yxx
    test_migrate_fpaper
    test_get_type
    -- test_mult_migrate 

    --more tests:
    -- test_typechecking
    -- test_mult_migrate
    -- test_the_next_terms
    -- test_migration_limit
    -- test_get_type
    -- test_const_gen
    -- test_simPrec
    -- test_simMatch
    -- test_pleaseUnify
    -- test_filter_consist
    -- test_apply_unifier
    -- test_simCon
    -- test_composition
    -- test_filter_isJust
    -- test_boundedness_sing
    -- test_boundnessOneSet
    -- test_boundness
    -- test_migrate_fpaper
    -- test_evil


termit :: String -> Expr -> IO () -> Spec
termit str term test =
    it (str ++ ": " ++ show term) test

test_the_next_terms :: Spec
test_the_next_terms = describe "finding the next well typed terms" $ do
    let c =  (App (Lam Tdyn "x" (Vv "x")) (Vi 3))
    let c' = (App (Lam Tint "x" (Vv "x")) (Vi 3))
    let self_application = (Lam Tdyn "x" (App (Vv "x") (Vv "x")))
    let self_application_next = (Lam (Tdyn ~> Tdyn) "x" (App (Vv "x") (Vv "x")))
    let self_application_dyn1 = (Lam ((Tdyn ~> Tdyn) ~> Tdyn) "x" (App (Vv "x") (Vv "x")))
    let self_application_dyn2 = (Lam (Tdyn ~> Tdyn ~> Tdyn) "x" (App (Vv "x") (Vv "x")))
    let self_application_int = (Lam (Tdyn ~> Tint) "x" (App (Vv "x") (Vv "x")))
    let self_application_bool = (Lam (Tdyn ~> Tbool) "x" (App (Vv "x") (Vv "x")))


    example c tenv [c']
    example self_application tenv [self_application_next]
    example self_application_next tenv [self_application_dyn1, 
                                        self_application_dyn2, 
                                        self_application_int, 
                                        self_application_bool]

    where 
        example term env val = 
            termit "the next well typed term" term $ do
                (get_the_next_well_typed_term term env) `shouldBe` val



test_get_type :: Spec
test_get_type = describe "Typecheck (fig 7)" $ do
    example (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))) (Just (Tdyn ~> Tdyn))
    example succ_lam_true_max (Just ((Tdyn ~> Tint) ~> Tint))
    example my_lam_max (Just ((Tdyn ~> Tint) ~> Tint))
    example simple_app_max (Just Tint)
    example (App (Vv "succ") (App(Lam Tint "y" (Vv "y"))
                (App (Lam Tdyn "x" (Vv "x"))(Vb True)))) (Just Tint)
    example (Lam Tint "x" (Vv "x")) (Just (Tint ~> Tint))
    example lam_xyy_max2 (Just (Tint ~> (Tint ~> Tint ~> Tint) ~> Tint)) 
    example evil_m (Just (Tdyn ~> Tdyn))
    example evil_example_max (Just (Tint ~> Tint))

    where 
     example term expected = do 
            it ("sees that " ++ show term ++ " has type = " ++ show (fromJust expected)) $ do
                (typecheck term tenv) `shouldBe` expected
  
test_typechecking :: Spec
test_typechecking = describe "type checking" $ do
    let c = Lam Tdyn "x" (Vv "x")
    let a = (App (App c c) c)
    let my_lam_succ = (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") x_true)))
    let self_application = (Lam (Tdyn ~> Tbool) "x" (App (Vv "x") (Vv "x")))
    let my_succ_app2 = (App (Vv "succ") x_true)
    let my_succ_app3 = (App (Vv "x") my_succ_app2)
    let my_succ = (Lam Tdyn "x" my_succ_app3)
    let app3 = (App (Lam Tdyn "x" (Vv "x")) (Vi 3))

    example a tenv True
    example my_lam_succ tenv True
    example self_application tenv True
    example x_true (("x", Tdyn):tenv) True
    example my_succ tenv True
    example app3 tenv True
    example lam tenv True
    example lam_xyy tenv True
    example succ_lam tenv True
    example (make_mapping f1) tenv True
    example lam_term_1 tenv True
    example app_term_2 tenv True

    where 
        example term env val = 
            termit "typechecks" term $ do
                (type_checks term env) `shouldBe` val

--the singleton checker
test_maximality :: Spec
test_maximality = describe "Singleton check" $ do
    
    --main tests
    example (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))) True
    example succ_lam_true False
    example my_lam False
    example simple_app False
    example (App (Vv "succ") (App(Lam Tdyn "y" (Vv "y"))
                (App (Lam Tdyn "x" (Vv "x"))(Vb True)))) False
    example (Lam Tdyn "x" (Vv "x")) False
    example lam_xyy False
    example evil False
    example evil_example False
    example self_application False
    example lam_term_1 False
    example app_term_2 False


    --scalability
    -- example (make_mapping f1) False
    -- example (make_mapping f2) False
    -- example (make_mapping f3) False
    -- example (make_mapping f4) False
    -- example (make_mapping f5) False
    -- example (make_mapping f6) False
    -- example (make_mapping f7) False
    -- example (make_mapping f8) False

    where 
        example :: Expr -> Bool -> Spec
        example term expected = do 
            it ("sees that " ++ show term ++ " is singleton? = " ++ show expected) $ do
                ismaximal term tenv `shouldBe` expected




test_topchoice :: Spec
test_topchoice = describe "Top choice check" $ do
    

    example (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))) True
    example succ_lam_true  True
    example my_lam True
    example simple_app True
    example (App (Vv "succ") (App(Lam Tdyn "y" (Vv "y"))
                (App (Lam Tdyn "x" (Vv "x"))(Vb True)))) False
    example (Lam Tdyn "x" (Vv "x")) False
    example lam_xyy False
    example evil False
    example evil_example False
    example self_application False
    example lam_term_1 False
    example app_term_2 False

    where 
        example :: Expr -> Bool -> Spec
        example term expected = do 
            it ("sees that " ++ show term ++ " has a top choice? =  " ++ show expected) $ do
                (length(topchoice term tenv) == 1) `shouldBe` expected






test_has_max :: Spec
test_has_max = describe "Maximality check (benchmarks 1-10)" $ do
    
    example (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))) True
    example succ_lam_true  True
    example my_lam True
    example simple_app True
    example (App (Vv "succ") (App(Lam Tdyn "y" (Vv "y"))
                (App (Lam Tdyn "x" (Vv "x"))(Vb True)))) True
    example (Lam Tdyn "x" (Vv "x")) True
    example lam_xyy True
    example evil True
    example evil_example True
    example self_application False


    it "should handle x" $ do
        "x" `shouldBe` "x"

    where 
        example :: Expr -> Bool -> Spec
        example term expected = do 
            it ("sees that " ++ show term ++ " has max? = " ++ show expected) $ do
                isJust (closestMaximalMigration_n term 5 tenv) `shouldBe` expected


test_has_max_large :: Spec
test_has_max_large = describe "Maximality check (benchmarks 11, 12 & NPHard examples) " $ do

    example lam_term_1 False
    example app_term_2 False
    example (make_mapping fpaper) True
    example (make_mapping f8) False
   

    where 
        example :: Expr -> Bool -> Spec
        example term expected = do 
            it ("sees that " ++ show term ++ " has max? = " ++ show expected) $ do
                isJust (closestMaximalMigration_n term 4 tenv) `shouldBe` expected


test_migrate_semi :: Spec
test_migrate_semi = describe "Show migrations (fig 6) benchmarks 1-9" $ do
    


    example (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))) (Just (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))))
    example succ_lam_true  (Just succ_lam_true_max)
    example my_lam (Just my_lam_max)
    example simple_app (Just simple_app_max)
    example (App (Vv "succ") (App(Lam Tdyn "y" (Vv "y"))
                (App (Lam Tdyn "x" (Vv "x"))(Vb True))))  
            (Just (App (Vv "succ") (App(Lam Tint "y" (Vv "y"))
                (App (Lam Tdyn "x" (Vv "x"))(Vb True)))))
    example (Lam Tdyn "x" (Vv "x"))  (Just (Lam Tint "x" (Vv "x")))
    example lam_xyy (Just lam_xyy_max)
    example evil (Just evil_m)
    example evil_example (Just evil_example_max)


    where 
        example :: Expr -> Maybe Expr -> Spec
        example term expected = do 
            it ("sees that " ++ show term ++ " has a maximal migration " ++ show (fromJust expected)) $ do
                (closestMaximalMigration term tenv) `shouldBe` expected



test_migrate :: Spec
test_migrate = describe "Show migrations (fig 6) benchmark 10" $ do
    

    example self_application Nothing


    where 
        example :: Expr -> Maybe Expr -> Spec
        example term expected = do 
            it ("sees that " ++ show term ++ " has a maximal migration " ++ show expected) $ do
                closestMaximalMigration_n term 5 tenv `shouldBe` expected



test_migrate_large :: Spec
test_migrate_large = describe "Show migrations (fig 6) 11,12 and f8" $ do
    
    example lam_term_1 Nothing
    example app_term_2 Nothing
    example (make_mapping f8) Nothing

   

    where 
        example :: Expr -> Maybe Expr -> Spec
        example term expected = do 
            it ("sees that " ++ show term ++ " has a maximal migration " ++ show expected) $ do
                closestMaximalMigration_n term 4 tenv `shouldBe` expected


test_migrate_fpaper :: Spec
test_migrate_fpaper = describe "NP hard example E_f" $ do
    
    example (make_mapping fpaper) True



    where 
        example :: Expr -> Bool -> Spec
        example term expected = do 
            it ("sees that " ++ show term ++ " has a maximal migration " ++ show (closestMaximalMigration term tenv)) $ do
                (ismaximal (fromJust (closestMaximalMigration term tenv)) tenv) `shouldBe` True



test_migration_limit :: Spec
test_migration_limit = describe "migration limit" $ do


    --infinite lattice maximal migration
    let identity = (Lam Tdyn "x" (Vv "x"))

    let my_succ_app2 = (App (Vv "succ") x_true)
    let my_succ_app3 = (App (Vv "x") my_succ_app2)
    let my_succ = (Lam Tdyn "x" my_succ_app3)

    let app_y = (Lam Tdyn "y" (Vv "x"))
    let app_x = (App app_y (Vv "x"))
    let app_xx = (App app_x (Vv "x"))
    let lam = (Lam Tdyn "x" app_xx)
    
    --terms with no maximal migration
    let self_application = (Lam Tdyn "x" (App (Vv "x") (Vv "x")))

    --terms with a finite lattice
    let finite_applications = (App (Lam Tdyn "x" (Vv "x")) (Vi 3))

    --term with many applications
    let app_yxx2 = (App (Vv "succ") (App  (Vv "y") (App (Vv "x") (Vv "x"))))
    let lam_xy2 = (Lam Tdyn "x" (Lam Tdyn "y" app_yxx2))


    example (Lam Tdyn "y" (App (App (Vv "y") (Vi 0)) (Vi 0))) 2
    example lam_xyy 2
    example identity 0
    example max_final 10
    example my_succ 4
    example self_application 1
    example (App self_application self_application) 3
    example finite_applications 1
    example lam 2
    example (App identity (Vi 4)) 1
    example evil_example 4
    example lam_xy2 4

    where 
        example :: Expr -> Int -> Spec
        example term expected = do 
            it (show term ++ " has a migration limit of " ++ show expected) $ do
                migration_limit term (("x",Tdyn ~> Tint):tenv) `shouldBe` expected



--CONSTRAINTS TESTS

test_const_gen :: Spec
test_const_gen = describe "constraint generation" $ do
    
    it "should handle x" $ do
        "x" `shouldBe` "x"

    let e = (Vi 4)
    let i = (Lam Tdyn "x" (Vv "x"))
    let ap = (App i e)


    example e [((CVar 0) .= CInt)]
    example i [(CVar 0) .= ((CVar 1) .~> (CVar 2)),
                                     (CDyn .<= (CVar 1)), 
                                     ((CVar 2) .= (CVar 1) )]
    example ap [(CVar 1) .|> ((CVar 5) .~> (CVar 0)),
                ((CVar 5) .~ (CVar 4)), 
                (CVar 1) .= ((CVar 2) .~> (CVar 3)),
                 CDyn .<= (CVar 2),
                 (CVar 3) .= (CVar 2),
                 (CVar 4) .= CInt]
 
    example succ_lam [(CVar 0) .= ((CVar 1) .~> (CVar 2)),
                      CDyn .<= (CVar 1),
                      (CVar 3) .|> ((CVar 5) .~> (CVar 2)),
                      (CVar 5) .~ (CVar 4),
                      (CVar 3) .= (CInt .~> CInt),
                      (CVar 4) .= (CVar 1)]

    example succ_lam_true [(CVar 0) .= ((CVar 1) .~> (CVar 2)),
                           CDyn .<= (CVar 1),
                           (CVar 3) .|> ((CVar 11) .~> (CVar 2)),
                           (CVar 11) .~ (CVar 4),
                           (CVar 3) .= (CVar 1),
                           (CVar 5) .|> ((CVar 10) .~> (CVar 4)),
                           (CVar 10) .~ (CVar 6),
                           (CVar 5) .= (CInt .~> CInt),
                           (CVar 7) .|> ((CVar 9) .~> (CVar 6)),
                           (CVar 9) .~ (CVar 8),
                           (CVar 7) .= (CVar 1),
                           (CVar 8) .= CBool]


    example lam_xx [(CVar 0) .= ((CVar 1) .~> (CVar 2)), 
                    CDyn .<= (CVar 1),
                    (CVar 3) .|> ((CVar 5) .~> (CVar 2)),
                    (CVar 5) .~ (CVar 4),
                    (CVar 3) .= (CVar 1),
                    (CVar 4) .= (CVar 1)]

              
    where 
        example :: Expr  ->  [Constraint] -> Spec
        example term expected = do 
            it ("sees that " ++ show term ++ " generates " ++ show expected) $ do
                (snd (constraint term tenv)) `shouldBe` expected


test_simPrec :: Spec
test_simPrec = describe "SimPrec" $ do
    
    it "should handle x" $ do
        "x" `shouldBe` "x"

    let constraints = (constraint succ_lam_true tenv)
    let constraints_ex2 = (constraint lam_xx tenv)
    let constraints_map1 = (constraint (make_mapping f1) tenv)

    let c2 = ((CVar 2), [(CInt .~> CInt) .<= (CVar 0),
                         (CBool .~> CBool) .<= (CVar 1), 
                         CDyn .<= (CVar 2)])


    example constraints (fst constraints, (delete (CDyn .<= (CVar 1)) 
                                                  (snd constraints)))

    example constraints_ex2 (fst constraints_ex2,(delete (CDyn .<= (CVar 1))(delete (CDyn .<= (CVar 2)) 
                                                  (snd constraints_ex2))))

    -- example constraints ((CVar 2),[])
    example c2 ((CVar 6), [(CVar 0) .= ((CVar 3) .~> (CVar 4)),
                            (CVar 3) .= CInt,
                            (CVar 4) .= CInt,
                            (CVar 1) .= ((CVar 5) .~> (CVar 6)),
                            (CVar 5) .= CBool,
                            (CVar 6) .= CBool ])


    where 
        example :: (CType, [Constraint])  -> (CType, [Constraint]) -> Spec
        example c expected = do 
            it ("sees that " ++ show c ++ " simplifies to " ++ show expected) $ do
                (fixed simPrec c)`shouldBe` expected



test_simMatch :: Spec
test_simMatch = describe "simMatch" $ do
    
    it "should handle x" $ do
        "x" `shouldBe` "x"

   
    example (Lam Tdyn "x" (Vv "x")) tenv [[CVar 0 .= ((CVar 1) .~> (CVar 2)),
                                           CVar 2 .= CVar 1]]

    example2 [CVar 0 .= ((CVar 1) .~> (CVar 2)),CVar 2 .= CVar 1]
        [[CVar 0 .= ((CVar 1) .~> (CVar 2)),CVar 2 .= CVar 1]]

    example2 [(CVar 5) .|> ((CVar 10) .~> (CVar 4))]
        [ [(CVar 5) .= ((CVar 10) .~> (CVar 4))]
        , [CVar 5 .= CDyn, CVar 10 .= CDyn, CVar 4 .= CDyn]
        ]


    -- example (make_mapping f1) tenv []

    where 
        example :: Expr  -> Env -> [[Constraint]] -> Spec
        example expr env expected = do 
            it ("sees that " ++ show expr ++ " simplifies matching to " ++ show expected) $ do
                (compose_upto_match expr env)`shouldBe` expected

        example2 :: [Constraint]  -> [[Constraint]] -> Spec
        example2 con expected = do 
            it ("sees that " ++ show con ++ " simplifies matching to " ++ show expected) $ do
                (simMatch con)`shouldBe` expected


test_pleaseUnify :: Spec
test_pleaseUnify = describe "Unifies to" $ do

    it "should handle x" $ do
        "x" `shouldBe` "x"

    let const_gen = (simMatch (snd (fixed simPrec (constraint lam_xx tenv))))
    let const_eq1 = (head const_gen)

    let lam_succ_cnst =(simMatch (snd (fixed simPrec (constraint succ_lam_true tenv))))
    let const_eq_lam_1 = lam_succ_cnst !! 0


    example const_eq_lam_1  lam_succ_unify0


    example const_eq1 (Right  [(0, ((CVar 5 .~> CVar 2) .~> CVar 2)),
                               (1, (CVar 5 .~> CVar 2)),
                               (3, (CVar 5 .~> CVar 2)),
                               (4, (CVar 5 .~> CVar 2))])



    where 
        example :: [Constraint]  -> Either String [(Int, CType)] -> Spec
        example c expected = do 
            it ("sees that " ++ show c ++ " unifies to " ++ show expected) $ do
                (pleaseUnify c) `shouldBe` expected


test_filter_consist :: Spec
test_filter_consist = describe "Filter consistenct constraints" $ do

    it "should handle x" $ do
        "x" `shouldBe` "x"

    let lam_succ_cnst =(simMatch (snd (fixed simPrec (constraint succ_lam_true tenv))))
    let const_eq_lam_1 = lam_succ_cnst !! 0

    example const_eq_lam_1 [(CVar 11) .~ (CVar 4), 
                            (CVar 10) .~ (CVar 6), 
                            (CVar 9) .~ (CVar 8)]

 where 
        example :: [Constraint]  -> [Constraint] -> Spec
        example c expected = do 
            it ("sees that " ++ show c ++ " filters consistency to " ++ show expected) $ do
                (getConsistConst c) `shouldBe` expected


test_apply_unifier :: Spec
test_apply_unifier = describe "Apply unifier to consistency" $ do
    
    --example 1
    example (getConsistConst const_eq_lam_0)  (fromRight [] lam_succ_unify0) 
                                               [(CVar 11) .~ CInt,
                                                CInt .~ (CVar 2),
                                                (CVar 11) .~ CBool]

    
    example const_eq_lam_5 (fromRight [] lam_succ_unify5 ) [CDyn .~ CInt,
                                                            CInt .~ CDyn,
                                                            CDyn .~ CBool]


    example const_eq_lam_xx_0 (fromRight [] lam_xx_unify0) [CVar 5 .~ (CVar 5 .~> CVar 2)]


    example app_xy_succ_true_cnst_0 (fromRight [] app_xy_succ_true_cnst_unify0)  
                                        [CInt .~ CVar 4, 
                                         CVar 4 .~ CVar 8,
                                         CVar 8 .~ CBool]

    -- example (evil_simMatch !! 0) (fromRight [] (pleaseUnify (evil_simMatch !! 2))) []


    it "should handle x" $ do
        "x" `shouldBe` "x"



    where 
        example :: [Constraint] -> [(Int, CType)]  -> [Constraint] -> Spec
        example c sol expected = do 
            it ("sees that " ++ show c ++ " applies consistenct constraints "
                                       ++ show expected) $ do
                fixed_uni apply_unifier c sol `shouldBe` expected



test_simCon :: Spec
test_simCon = describe "Simplify constraints" $ do
    
    example [] (Just [])

    -- --example 1

    example  [(CVar 11) .~ CInt, CInt .~ (CVar 2), (CVar 11) .~ CBool] 
              (Just [(CVar 11) .~ CInt, (CVar 2) .~ CInt, (CVar 11) .~ CBool]  )
                                              

    example [CDyn .~ CInt,
             CInt .~ CDyn,
             CDyn .~ CBool] (Just[])


    example [CVar 5 .~ (CVar 5 .~> CVar 2)] (Just [CVar 5 .~ (CVar 5 .~> CVar 2)])


    example [CInt .~ CVar 4, CVar 4 .~ CVar 8, CVar 8 .~ CBool]  (Just [CVar 4 .~ CInt, CVar 4 .~ CVar 8, CVar 8 .~ CBool])



    it "should handle x" $ do
        "x" `shouldBe` "x"

    where 
        example :: [Constraint] -> Maybe [Constraint] -> Spec
        example c expected = do 
            it ("sees that " ++ show c ++ " applies consistenct constraints "
                                       ++ show expected) $ do
                fixedM simCon c  `shouldBe` expected
   


test_composition :: Spec
test_composition = describe "composes upto consistency to" $ do
    
    example lam_xx [Just [CVar 5 .~ (CVar 5 .~> CVar 2)],
                                                     Just []]

    example succ_lam_true [Just [CVar 11 .~ CInt,CVar 2 .~ CInt, CVar 11 .~ CBool],Just []]

    example app_xy_succ_true [Just [CVar 4 .~ CInt,CVar 4 .~ CVar 8,
                                         CVar 8 .~ CBool]]

    -- example (make_mapping f1) [Nothing]

    -- example evil [Nothing]

    it "should handle x" $ do
        "x" `shouldBe` "x"

    where 
        example :: Expr  -> [Maybe [Constraint]] -> Spec
        example expr expected = do 
            it ("sees that " ++ show expr ++ " composes constraints into (final step) "
                                       ++ show expected) $ do
                compose_all expr tenv  `shouldBe` expected


test_filter_isJust :: Spec
test_filter_isJust  = describe "re-writes the constraints" $ do
    
    it "should handle x" $ do
        "x" `shouldBe` "x"

    example [Just [CVar 5 .~ (CVar 5 .~> CVar 2)],Just [], Nothing] 
            [[CVar 5 .~ (CVar 5 .~> CVar 2)],[]]


    where 
        example :: [Maybe [Constraint]] -> [[Constraint]] -> Spec
        example cnst expected = do 
            it ("sees that " ++ show cnst ++ " re-writes constraints without Maybe "
                                       ++ show expected) $ do
                filter_isjust cnst `shouldBe` expected



test_boundedness_sing :: Spec
test_boundedness_sing  = describe "boundedness for one variable" $ do
    
    it "should handle x" $ do
        "x" `shouldBe` "x"

    example (CVar 5) [CVar 5 .~ (CVar 5 .~> CVar 2)] False
    example (CVar 2) [CVar 11 .~ CInt,CVar 2 .~ CInt, CVar 11 .~ CBool] True
    example (CVar 11) [CVar 11 .~ CInt,CVar 2 .~ CInt, CVar 11 .~ CBool] True
    example (CVar 0) [CVar 0 .~ (CVar 1 .~> CVar 2),
                      CVar 1 .~ CInt,
                      CVar 2 .~ CInt] False

    example (CVar 4) [CVar 4 .~ CInt, CVar 4 .~ CVar 8, CVar 8 .~ CBool] True
    example (CVar 8) [CVar 4 .~ CInt, CVar 4 .~ CVar 8, CVar 8 .~ CBool] True

    example (CVar 0) [CVar 0 .~ (CInt .~> CVar 1), CVar 0 .~ (CVar 2 .~> CBool)] True


    where 
        example :: CType -> [Constraint] -> Bool -> Spec
        example typ cnst_lst expected = do 
            it ("sees that " ++ show typ ++ show cnst_lst ++ " boundness for one var is "
                                       ++ show expected) $ do
                boundnessOneVar typ cnst_lst 2 `shouldBe` expected



test_boundnessOneSet :: Spec
test_boundnessOneSet  = describe "boundedness for one set of constraints" $ do
    
    it "should handle x" $ do
        "x" `shouldBe` "x"

    let c1 = [CVar 5 .~ (CVar 5 .~> CVar 2)] 
    let c2 = [CVar 11 .~ CInt,CVar 2 .~ CInt, CVar 11 .~ CBool]
    let c3 = [CVar 0 .~ (CVar 1 .~> CVar 2),
                      CVar 1 .~ CInt,
                      CVar 2 .~ CInt]

    let c4 = [CVar 4 .~ CInt, CVar 4 .~ CVar 8, CVar 8 .~ CBool]



    example c1 c1 False
    example c2 c2 True
    example c3 c3 False
    example c4 c4 True

    where 
        example :: [Constraint] -> [Constraint]  -> Bool -> Spec
        example cnst_lst1 cnst_lst2 expected = do 
            it ("sees that " ++ show cnst_lst2 ++ " boundness for one var is "
                                       ++ show expected) $ do
                boundnessOneSet cnst_lst1 cnst_lst2 `shouldBe` expected



test_boundness :: Spec
test_boundness  = describe "boundedness for constraints" $ do
    
    it "should handle x" $ do
        "x" `shouldBe` "x"

    let c1 = [CVar 5 .~ (CVar 5 .~> CVar 2)] 
    let c2 = [CVar 11 .~ CInt,CVar 2 .~ CInt, CVar 11 .~ CBool]
    let c3 = [CVar 0 .~ (CVar 1 .~> CVar 2),
                      CVar 1 .~ CInt,
                      CVar 2 .~ CInt]

    let c4 = [CVar 4 .~ CInt, CVar 4 .~ CVar 8, CVar 8 .~ CBool]
    let c5 = [CVar 0 .~ (CInt .~> CVar 1),
             CVar 0 .~ (CVar 2 .~> CBool)]


    let i_n = (filter_isjust (compose_all (Lam Tdyn "x" (Vv "x")) tenv)) 



    example [c1] False
    example [c2] True
    example [c3] False
    example [c4] True
    example [c5] True --questionable bec. what if there are variables on the RHS but not on LHS?
    example i_n True


    where 
        example :: [[Constraint]] -> Bool -> Spec
        example cnst_lst expected = do 
            it ("sees that " ++ show cnst_lst ++ " is boundness = "
                                       ++ show expected) $ do
                boundedness cnst_lst `shouldBe` expected




test_finitness :: Spec
test_finitness  = describe "Finitness check" $ do
    
    example (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))) True
    example succ_lam_true True
    example my_lam True
    example simple_app True
    example (App (Vv "succ") (App(Lam Tdyn "y" (Vv "y"))
                (App (Lam Tdyn "x" (Vv "x"))(Vb True)))) True
    example (Lam Tdyn "x" (Vv "x")) False
    example lam_xyy False
    example evil False
    example evil_example False
    example self_application False
    example lam_term_1 False
    example app_term_2 False


    -- example final True
    -- example my_lam True
    -- example lam False
    -- example simple_app True
    -- example lam_xyy False
    -- example evil_example False
    -- example (Lam Tdyn "x" (Vv "x")) False
    -- example self_application False
    -- example succ_lam_true True
    -- example evil False
    -- example (Lam Tdyn "x" (App (Vv "x") my_succ)) True
    -- example (App (Vv "succ") 
    --             (App(Lam Tdyn "y" (Vv "y"))
    --                 (App (Lam Tdyn "x" (Vv "x"))(Vb True)))) True
    -- example (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))) True
    -- example lam_term_1 False
    -- example app_term_2 False


    -- scalability
    -- example (make_mapping f1) False

    where 
        example :: Expr -> Bool -> Spec
        example expr expected = do 
            it ("sees that " ++ show expr ++ " is finite? = "
                                       ++ show expected) $ do
                check_finitness expr tenv `shouldBe` expected



--in one of our benchmark, we do not use the closest migration we find.
-- this test shows that our tool finds the migration in level 5 of the lattice
test_lam_yxx :: Spec
test_lam_yxx= describe "find specific maximal migration" $ do
    
    example lam_xyy lam_xyy_max2  True
   

    where 
        example :: Expr -> Expr -> Bool -> Spec
        example expr1 expr2 expected = do 
            it ("sees that " ++ show expr2 ++ 
                " is a maximal migration for " ++ 
                show expr1) $ do
                 (elem expr2 (findAllMaximalMigrationsN 5 expr1  tenv)) `shouldBe` True


-- test_evil :: Spec
-- test_evil= describe "find specific maximal migration" $ do
    
--     example evil_example []  
   
--     it "should handle x" $ do
--         "x" `shouldBe` "x"

--     where 
--         example :: Expr  -> [Expr] -> Spec
--         example expr expected = do 
--             it ("sees that " ++ show expr ++ " has migrations"
--                                        ++ show expected) $ do
--                 findAllMaximalMigrations expr tenv `shouldBe` expected




test_mult_migrate :: Spec
test_mult_migrate = describe "find multiple migrations" $ do
    

    --migrations at level 3:
    let app_y1 = (Lam Tint "y" (Vv "x"))
    let app_x1 = (App app_y1 (Vv "x"))
    let app_xx1 = (App app_x1 (Vv "x"))
    let lam1 = (Lam Tdyn "x" app_xx1)


    let app_y2 = (Lam Tbool "y" (Vv "x"))
    let app_x2 = (App app_y2 (Vv "x"))
    let app_xx2 = (App app_x2 (Vv "x"))
    let lam2 = (Lam Tdyn "x" app_xx2)


    example 2 simple_app [(App (Lam Tint "x" (Vv "x")) (Vi 4))]
    example 3 lam [lam1, lam2]
    example 3 (make_mapping f8) []



    where 
        example :: Int -> Expr -> [Expr] -> Spec
        example lvl term expected = do 
            it ("sees that at level " ++ show lvl ++ " "  ++ 
                show term ++ " has migrations " ++ show expected) $ do
                findAllMaximalMigrationsN lvl term  tenv `shouldBe` expected






