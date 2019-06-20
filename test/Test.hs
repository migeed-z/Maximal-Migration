{-# Language QuasiQuotes #-}
module Main where

import Test.Hspec
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



import qualified Data.Map as Map

main :: IO ()
main = test

test :: IO ()
test = hspec $ do
    test_maximality
    test_typechecking
    test_migrate
    test_the_next_terms
    test_migration_limit
    test_get_type
    test_const_gen
    test_simPrec
    test_simMatch
    test_pleaseUnify
    test_filter_consist
    test_apply_unifier
    -- describe "lambda parser" $ do
    --     it "works" $ do
    --         [prog|\x:*. x|] `shouldBe` (Lam Tdyn "x" (Vv "x"))
    --     it "is the same" $ do
    --         [prog|(\x :*.x) 3|] `shouldBe` (App (Lam Tdyn "x" (Vv "x")) (Vi 3))

    describe "finding next term" $ do
        let c = (Lam (Tdyn ~> Tint) "x" (Vv "x"))
        it (show c) $ do
            get_the_next_term c `shouldMatchList` [
                -- [prog|λx : int -> int . x|]
                (Lam (Tint ~> Tint) "x" (Vv "x"))
              , (Lam (Tbool ~> Tint) "x" (Vv "x"))
              , (Lam ((Tdyn ~> Tdyn) ~> Tint) "x" (Vv "x"))
              ]

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
test_get_type = describe "type checking" $ do
    
    let x_true = (App (Vv "x") (Vb True))
    let my_succ_app2 = (App (Vv "succ") x_true)
    let my_succ_app3 = (App (Vv "x") my_succ_app2)
    let my_succ = (Lam Tdyn "x" my_succ_app3)

    example my_succ tenv (Just (Tdyn ~> Tdyn))
    -- example evil_example tenv Nothing

    where 
        example term env val = 
            termit "the type is" term $ do
                (typecheck term env) `shouldBe` val
  
test_typechecking :: Spec
test_typechecking = describe "type checking" $ do
    let c = Lam Tdyn "x" (Vv "x")
    let a = (App (App c c) c)
    let x_true = (App (Vv "x") (Vb True))
    let my_lam_succ = (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") x_true)))
    let self_application = (Lam (Tdyn ~> Tbool) "x" (App (Vv "x") (Vv "x")))


    let my_succ_app2 = (App (Vv "succ") x_true)
    let my_succ_app3 = (App (Vv "x") my_succ_app2)
    let my_succ = (Lam Tdyn "x" my_succ_app3)

    let app3 = (App (Lam Tdyn "x" (Vv "x")) (Vi 3))

    let app_y = (Lam Tdyn "y" (Vv "x"))
    let app_x = (App app_y (Vv "x"))
    let app_xx = (App app_x (Vv "x"))
    let lam = (Lam Tdyn "x" app_xx)


    example a tenv True
    example my_lam_succ tenv True
    example self_application tenv True
    example x_true (("x", Tdyn):tenv) True
    example my_succ tenv True
    example app3 tenv True
    example lam tenv True
    example lam_xyy tenv True
    example succ_lam tenv True

    where 
        example term env val = 
            termit "typechecks" term $ do
                (type_checks term env) `shouldBe` val


test_maximality :: Spec
test_maximality = describe "maximality" $ do
    example (Vi 4) True
    let x_4 = (App (Vv "x") (Vi 4))
    let x_true = (App (Vv "x") (Vb True))
    let my_succ = (App (Vv "succ") x_true)
    let my_succ2 = (App (Vv "succ") x_4)
    let lam_z = (Lam Tint "z" (Vb True))
    let first_app = (App lam_z my_succ)
    let lam_y = (Lam Tint "y" first_app)
    let appx  = (App lam_y my_succ2)
    let final = (Lam (Tdyn ~> Tint) "x" appx)


    -- let max_migraion = (Lam Tdyn "x" expr_max)
    -- let expr_max = ((Vv "x") True)

    example final True

    it "should handle x" $ do
        "x" `shouldBe` "x"


    where 
        example :: Expr -> Bool -> Spec
        example term expected = do 
            it ("sees that " ++ show term ++ " is maximal if " ++ show expected) $ do
                ismaximal term tenv `shouldBe` expected

test_migrate :: Spec
test_migrate = describe "max" $ do
    
    --term1
    let x_4 = (App (Vv "x") (Vi 4))
    let x_true = (App (Vv "x") (Vb True))
    let my_succ = (App (Vv "succ") x_true)
    let my_succ2 = (App (Vv "succ") x_4)
    let lam_z = (Lam Tdyn "z" (Vb True))
    let first_app = (App lam_z my_succ)
    let lam_y = (Lam Tdyn "y" first_app)
    let appx  = (App lam_y my_succ2)
    let final = (Lam Tdyn "x" appx)

    let max_x_true = (App (Vv "x") (Vb True))
    let max_my_succ = (App (Vv "succ") x_true)
    let max_my_succ2 = (App (Vv "succ") x_4)
    let max_lam_z = (Lam Tint "z" (Vb True))
    let max_first_app = (App max_lam_z max_my_succ)
    let max_lam_y = (Lam Tint "y" max_first_app)
    let max_appx  = (App max_lam_y max_my_succ2)
    let max_final = (Lam (Tdyn ~> Tint) "x" max_appx)
    

    --term 2
    let my_add = (App (App (Vv "+") x_4) x_true)
    let my_lam = (Lam (Tdyn) "x" my_add)
    let my_lam_max = (Lam (Tdyn ~> Tint) "x" my_add)


    --term 3 (infinite lattice with a maximal migration)
    let app_y = (Lam Tdyn "y" (Vv "x"))
    let app_x = (App app_y (Vv "x"))
    let app_xx = (App app_x (Vv "x"))
    let lam = (Lam Tdyn "x" app_xx)


    let app_y_max = (Lam Tint "y" (Vv "x"))
    let app_x_max = (App app_y_max (Vv "x"))
    let app_xx_max = (App app_x_max (Vv "x"))
    let lam_max = (Lam Tdyn "x" app_xx_max)


    --a single function application
    let simple_app = (App (Lam Tdyn "x" (Vv "x")) (Vi 4))
    let simple_app_max = (App (Lam Tint "x" (Vv "x")) (Vi 4))


    --term with many applications
    let app_yxx = (App (Vv "succ") (App (App (Vv "y") (Vv "x")) (Vv "x")))
    let lam_xy = (Lam Tdyn "x" (Lam Tdyn "y" app_yxx))



    --term with no maximal migration
    let self_application = (Lam Tdyn "x" (App (Vv "x") (Vv "x")))



    example final (Just max_final)
    example my_lam (Just my_lam_max)
    example lam (Just lam_max)
    example simple_app (Just simple_app_max)
    example lam_xyy (Just lam_xyy_max)
    example evil_example (Just evil_example_max)
    example (Lam Tdyn "x" (Vv "x")) (Just (Lam Tint "x" (Vv "x")))


    example self_application Nothing


    it "should handle x" $ do
        "x" `shouldBe` "x"

    where 
        example :: Expr -> Maybe Expr -> Spec
        example term expected = do 
            it ("sees that " ++ show term ++ " has a maximal migration " ++ show expected) $ do
                closestMaximalMigration term tenv `shouldBe` expected


test_migration_limit :: Spec
test_migration_limit = describe "migration limit" $ do


    --infinite lattice maximal migration
    let identity = (Lam Tdyn "x" (Vv "x"))
    let x_4 = (App (Vv "x") (Vi 4))
    let x_true = (App (Vv "x") (Vb True))
    let my_succ = (App (Vv "succ") x_true)
    let my_succ2 = (App (Vv "succ") x_4)
    let lam_z = (Lam Tint "z" (Vb True))
    let first_app = (App lam_z my_succ)
    let lam_y = (Lam Tint "y" first_app)
    let appx  = (App lam_y my_succ2)
    let final = (Lam (Tdyn ~> Tint) "x" appx)

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


    example (Lam Tdyn "y" (App (App (Vv "y") (Vi 0)) (Vi 0))) 2
    example lam_xyy 2
    example identity 0
    example final 10
    example my_succ 4
    example self_application 1
    example (App self_application self_application) 3
    example finite_applications 1
    example lam 2


    it "should handle x" $ do
        "x" `shouldBe` "x"

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


    -- example app_xy_succ_true []
              
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

    -- let constraints = (snd (fixed simPrec (constraint succ_lam_true tenv)))
   
    -- example constraints [[]]

    where 
        example :: [Constraint]  -> [[Constraint]] -> Spec
        example c expected = do 
            it ("sees that " ++ show c ++ " simplifies matching to " ++ show expected) $ do
                (simMatch c)`shouldBe` expected

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


    -- example const_eq_lam_1 (Right [])

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

--todo
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

    --example 2
    -- example (getConsistConst )                                                


    it "should handle x" $ do
        "x" `shouldBe` "x"



    where 
        example :: [Constraint] -> [(Int, CType)]  -> [Constraint] -> Spec
        example c sol expected = do 
            it ("sees that " ++ show c ++ " applies consistenct constraints "
                                       ++ show expected) $ do
                (apply_unifier c sol) `shouldBe` expected

    -- let e = (Vi 4)
    -- let i = (Lam Tdyn "x" (Vv "x"))
    -- let ap = (App i e)

    -- example e [((CVar 0) .= CInt)]
    -- example i [(CVar 0) .= ((CVar 1) .~> (CVar 2)),
    --                                  (CDyn .<= (CVar 1)), 
    --                                  ((CVar 2) .= (CVar 1) )]
    -- example ap [(CVar 1) .|> ((CVar 5) .~> (CVar 0)),
    --             ((CVar 5) .~ (CVar 4)), 
    --             (CVar 1) .= ((CVar 2) .~> (CVar 3)),
    --              CDyn .<= (CVar 2),
    --              (CVar 3) .= (CVar 2),
    --              (CVar 4) .= CInt]
 
    -- example succ_lam [(CVar 0) .= ((CVar 1) .~> (CVar 2)),
    --                   CDyn .<= (CVar 1),
    --                   (CVar 3) .|> ((CVar 5) .~> (CVar 2)),
    --                   (CVar 5) .~ (CVar 4),
    --                   (CVar 3) .= (CInt .~> CInt),
    --                   (CVar 4) .= (CVar 1)]

    -- example succ_lam_true [(CVar 0) .= ((CVar 1) .~> (CVar 2)),
    --                        CDyn .<= (CVar 1),
    --                        (CVar 3) .|> ((CVar 11) .~> (CVar 2)),
    --                        (CVar 11) .~ (CVar 4),
    --                        (CVar 3) .= (CVar 1),
    --                        (CVar 5) .|> ((CVar 10) .~> (CVar 4)),
    --                        (CVar 10) .~ (CVar 6),
    --                        (CVar 5) .= (CInt .~> CInt),
    --                        (CVar 7) .|> ((CVar 9) .~> (CVar 6)),
    --                        (CVar 9) .~ (CVar 8),
    --                        (CVar 7) .= (CVar 1),
    --                        (CVar 8) .= CBool]


    -- example lam_xx [(CVar 0) .= ((CVar 1) .~> (CVar 2)), 
    --                 CDyn .<= (CVar 1),
    --                 (CVar 3) .|> ((CVar 5) .~> (CVar 2)),
    --                 (CVar 5) .~ (CVar 4),
    --                 (CVar 3) .= (CVar 1),
    --                 (CVar 4) .= (CVar 1)]




    -- it "should handle x" $ do
    --     pleaseUnify [] `shouldBe` Right []

--ex1
succ_lam_true =  (Lam Tdyn "x" (App (Vv "x") 
                 (App (Vv "succ") (App (Vv "x") (Vb True)))))

lam_succ_cnst =(simMatch (snd (fixed simPrec (constraint succ_lam_true tenv))))
const_eq_lam_0 = lam_succ_cnst !! 0
lam_succ_unify0 =  (pleaseUnify const_eq_lam_0)

const_eq_lam_5 = lam_succ_cnst !! 5
lam_succ_unify5 =  (pleaseUnify const_eq_lam_5)


--ex2
lam_xx = (Lam Tdyn "x" (App (Vv "x") (Vv "x")))
lam_xx_cnst =(simMatch (snd (fixed simPrec (constraint lam_xx tenv))))
const_eq_lam_xx_0 = lam_xx_cnst !! 0
lam_xx_unify0 = (pleaseUnify const_eq_lam_xx_0)


-- succ((λy.y)((λx.x)true)) 

--ex3
app_xy_succ_true = (App (Vv "succ") 
                    (App (Lam Tdyn "y" (Vv "y")) 
                      (App (Lam Tdyn "x" (Vv "x")) (Vb True))))  

app_xy_succ_true_cnst =(simMatch (snd (fixed simPrec (constraint app_xy_succ_true tenv))))
app_xy_succ_true_cnst_0 = app_xy_succ_true_cnst !! 0
app_xy_succ_true_cnst_unify0 = (pleaseUnify app_xy_succ_true_cnst_0)



succ_lam = (Lam Tdyn "x" (App (Vv "succ") (Vv "x")))

succ_app = (App (Vv "succ") (App (Lam Tdyn "y" (Vv "y")) 
           (App (Lam Tdyn "x" (Vv "x")) (Vb True)) ) )

lam_xyy = 
    Lam Tdyn "x" (Lam Tdyn "y" app_yxx)
    where
        app_yxx = (App (App (Vv "y") (Vv "x")) (Vv "x"))

lam_xyy_max =
    Lam Tint "x" (Lam (Tint ~> Tdyn ~> Tdyn) "y" app_yxx)
    where
        app_yxx = (App (App (Vv "y") (Vv "x")) (Vv "x"))

evil_example = 
    (Lam Tdyn "x"
        (App ((Lam (Tdyn) "f" 
                    (App (App const (Vv "f"))
                        (App (Vv "f") (Vv "x")))))
            (Lam Tdyn "z" (Vi 1))
        ))


    where 
        const = (Lam Tdyn "x" (Lam Tdyn "y" (Vv "x")))   


evil_example_max = 
    (Lam Tint "x"
        (App ((Lam (Tdyn) "f" 
                    (App (App const (Vv "f"))
                        (App (Vv "f") (Vv "x")))))
            (Lam Tint "z" (Vi 1))
        ))


    where 
        const = (Lam Tint "x" (Lam Tint "y" (Vv "x")))   



-- 5
-- type_prec_test = do
--     print(typ_precision Tdyn Tdyn)
--     print(typ_precision Tdyn (Tint ~> Tint))
--     print(typ_precision (Tint ~> Tint) Tdyn)

-- term_prec_test = do
--     let c = Lam Tdyn "x" (Vv "x")
--     let c' = Lam Tint "x" (Vv "x")
--     let c'' = Lam Tint "x" (Vv "y")
--     print(term_precision c c')
--     print(term_precision c' c)
--     print(term_precision c c'')
