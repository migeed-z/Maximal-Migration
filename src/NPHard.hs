{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module NPHard where
import Formula
import Lang
import Data.List 




make_mapping :: LFormula -> Expr
make_mapping f = (make_lam
                 ((length f) - 1)
                 ((length f) - 1)
                 f)

make_lam :: Int -> Int -> LFormula -> Expr
make_lam n1 n2 f=
 case n1 of 
  0 ->
    Lam 
      (Tdyn ~> Tint) 
      ("v" ++ (show 0)) 
      (make_body n2 f)
  n -> 
    Lam 
      (Tdyn ~> Tint)
      ("v" ++ (show n))
      (make_lam (n-1) n2 f)


clauseLiterals :: Clause -> [Literal]
clauseLiterals (Cl l1 l2 l3) = [l1, l2, l3]

collect_vars :: LFormula -> [String]
collect_vars = 
  nub . concatMap (map (literalNameAsString . nameOfLiteral) . clauseLiterals)


--check if a literal occurrs in a clause
check_occ_lit :: Literal -> Clause -> Bool
check_occ_lit l (Cl l1 l2 l3) = 
  l == l1 || l == l2 || l == l3

litvar :: (String -> String) -> LiteralName -> Expr
litvar fn l = Vv (fn $ literalNameAsString l)

makeNegVar :: LiteralName -> LFormula -> Expr
makeNegVar l = 
  foldr (\i -> App (Vv "+" !$ (var i !$ litvar ('¬':) l))) (Vi 0)
  . map fst
  . filter (check_occ_lit (Neg l) . snd) 
  . zip [0..]

  where
    (!$) = App  


makePosVar :: LiteralName -> LFormula -> Expr
makePosVar l = 
  foldr (\i -> App (Vv "+" !$ (var i !$ litvar id l))) (Vi 0)
  . map fst
  . filter (check_occ_lit (Pos l) . snd) 
  . zip [0..]

  where
    (!$) = App  



--Given a negative literal, make a lambda expr
make_neg_lam :: LiteralName -> LFormula -> Expr
make_neg_lam s f = 
  Lam Tdyn 
    ("¬"++ literalNameAsString s) 
    (App 
      (Lam Tint 
        (literalNameAsString $ nextLiteralName s) 
        (litvar ('¬':) s)
      )
      (makeNegVar s f)
    ) 

make_pos_lam_true :: LiteralName -> LFormula -> Expr
make_pos_lam_true s f = 
 (App (Lam Tdyn 
    (literalNameAsString s) 
    (App 
      (Lam Tint 
        (literalNameAsString $ nextLiteralName s) 
        (litvar id s)
      ) 
      (makePosVar s f)))(Vb True))



make_pos_neg_lam :: LiteralName -> LFormula -> Expr
make_pos_neg_lam s f = (App (make_neg_lam s f)
                            (make_pos_lam_true s f))


--can I add +0 here too?
make_pos_neg_lam_all :: [String] -> LFormula -> Expr
make_pos_neg_lam_all [] f = (Vi 0)
make_pos_neg_lam_all (x : xs) f = 
  (App (App (Vv "+") (make_pos_neg_lam (LiteralName x) f))
       (make_pos_neg_lam_all xs f))
                                  


make_app_vars :: Int -> LFormula -> Expr
make_app_vars n f = 
    case n of 
        0 -> (make_app_var 0)
        otherwise -> (App (App (Vv "+") 
                           (make_app_var n)) 
                                (make_app_vars (n-1) f))

make_app_var :: Int -> Expr
make_app_var i = (App (var i) (var i))


make_body :: Int -> LFormula -> Expr
make_body n f = 
  (App (App (Vv "+") (make_app_vars n f))
       (make_pos_neg_lam_all 
        (collect_vars f) f))               

var :: Int -> Expr
var n = (Vv ("v" ++ (show n)))

-- map_prog :: LFormula -> Expr
-- map_prog  = (Vi 3)


test_printer = do
  let c1 = Cl (Pos "x0") (Neg "x1") (Pos "x2")
  let c2 = Cl (Neg "x0") (Pos "x1") (Pos "x2")

  -- print (make_lam 1 1 [c1, c2])
  print (make_mapping [c1, c2])
  -- print(makeNegVar "x" [c1, c2, c3])
  -- print(make_lam 3 3)
  -- print (make_pos_neg_lam "x0" [c1, c2])
  -- print $ make_lam 3 3 []
  -- print $ make_neg_lam "x0" [c1, c2]
  -- print $ make_pos_lam_true "x0" [c1, c2]


  -- print $ make_neg_lam "x1" [c1, c2]
  -- print $ make_pos_lam_true "x1" [c1, c2]


  -- print $ make_neg_lam "x2" [c1, c2]
  -- print $ make_pos_lam_true "x2" [c1, c2]


  -- print $ collect_all_vars [c1, c2]

  -- print(make_app_vars 3)
  -- print(make_lam 3 3)


-- --takes a negative literal and a list of clauses
-- -- and makes negative exprs.
-- -- c is # of clauses - 1.
-- make_neg_var :: Literal -> LFormula -> Int -> Expr
-- make_neg_var l [] c = (Vi 0)
-- make_neg_var (Neg s) (x:xs) c = 
--   case check_occ_lit (Neg s) x of
--    True -> (App (App (Vv "+") (App (make_var (c-(length xs)))
--                                    (Vv("¬"++s)))) 
--                                    (make_neg_var (Neg s) xs c))
--    otherwise -> (make_neg_var (Neg s) xs c)


--takes a negative literal and a list of clauses
-- and makes negative exprs.
-- c is # of clauses - 1.
-- make_neg_var :: LiteralName -> LFormula -> Int -> Expr
-- make_neg_var l [] c = (Vi 0)
-- make_neg_var s (x:xs) c 
--   | check_occ_lit (Neg s) x = 
--     App 
--       (App (Vv "+") . App (var $ c - length xs) $ litvar ('¬':) s)
--       $ make_neg_var s xs c
--   | otherwise =
--     (make_neg_var s xs c)


 -- λv1 : * -> int . λv0 : * -> int .
 --  + (v1 v1) (v0 v0) 

-- λv1 : * -> int . λv0 : * -> int . 
--  + (v1 v1) (v0 v0) 
--  (+ ((λ¬x0 : * . (λx0' : int . ¬x0) (+ (v1 ¬x0) 0)) 
--     ((λx0 : * . (λx0' : int . x0) (+ (v0 x0) 0)) True)) 
--   (+ ((λ¬x1 : * . (λx1' : int . ¬x1) (+ (v0 ¬x1) 0)) ((λx1 : * . (λx1' : int . x1) (+ (v1 x1) 0)) True)) 
--     (+ ((λ¬x2 : * . (λx2' : int . ¬x2) 0) ((λx2 : * . (λx2' : int . x2) (+ (v0 x2) (+ (v1 x2) 0))) True)) 0)))














