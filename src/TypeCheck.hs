{-# Language ViewPatterns #-}
{-# Language LambdaCase #-}

module TypeCheck where

import Control.Monad (guard)

import Lang

typecheck :: Expr -> Env ->  Maybe Vtype
typecheck (Vv x) (envlookup x -> Just t) = Just t
typecheck (Vi e) _ = Just Tint
typecheck (Vb e) _ = Just Tbool
typecheck (Lam typ name term) env = do
    t2 <- typecheck term ((name,typ):env)
    Just (Tfun typ t2)
typecheck (App e1 e2) env = do
    t1 <- typecheck e1 env
    t2 <- typecheck e2 env
    Tfun t11 t12 <- matching t1
    guard (consist t11 t2)
    Just t12

typecheck _ _ = Nothing

envlookup :: Name -> Env ->  Maybe Vtype
envlookup name = \case 
    (n,t):xs 
        | n == name -> Just t
        | otherwise -> envlookup name xs 
    [] -> Nothing

--is t1 consistant with t2?
consist :: Vtype -> Vtype -> Bool
consist t1 t2  | t1==t2 = True
consist Tdyn t = True
consist t Tdyn = True
consist (Tfun t1 t2) (Tfun t1' t2') = 
    (consist t1 t1') &&
    (consist t2 t2')
consist _ _ = False

matching :: Vtype -> Maybe Vtype
matching (Tfun t1 t2) = Just (Tfun t1 t2)
matching Tdyn = Just (Tfun Tdyn Tdyn)
matching _ = Nothing

typ_precision :: Vtype -> Vtype -> Bool
typ_precision t1 t2 | t1 == t2 = True
typ_precision Tdyn t2 = True
typ_precision (Tfun t1 t2) (Tfun t1' t2') = 
    (typ_precision t1 t1') &&
    (typ_precision t2 t2')
typ_precision _ _ = False

term_precision :: Expr -> Expr -> Bool
term_precision e1 e2 | e1 == e2 = True
term_precision (Lam typ1 x1 e1) (Lam typ2 x2 e2) = 
    (typ_precision typ1 typ2) && 
    (term_precision e1 e2)
term_precision (App e1 e2) (App e1' e2') =
    (term_precision e1 e1') &&
    (term_precision e2 e2')
term_precision _ _ = False



