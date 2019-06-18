{-# LANGUAGE LambdaCase #-}

module Tree where


import Text.Show

import Lang
import Maximality

toTikzTree :: Int -> Expr -> Env -> String
toTikzTree n expr env =
  showEverything expr ""
  where
    showEverything expr = 
          showString "\\begin{tikzpicture}[grow=right, sloped]\n"
        . showString "\\" . showNode n expr env
        . showString ";"
        . showString "\\end{tikzpicture}\n"


    showNode n expr env =
        showString "node [" . showString nodeType
        . showString "] {$"
        . showLatexTerm expr
        . showString "$}\n"
        . ( if doesTypeCheck
            then foldr (\c f -> f . c) id $ map showChild children
            else id
            )

        where 
            children = get_the_next_term expr

            doesTypeCheck = type_checks expr env

            nodeType = 
                if doesTypeCheck 
                    then "mig"
                    else "notypecheck"
            
            showChild expr 
                | n == 0 = showString ""
                | otherwise = 
                    showString "child {\n"
                    . showNode (n - 1) expr env
                    . showString "edge from parent\n"
                    . showString "}\n"




showLatexTerm :: Expr -> ShowS
showLatexTerm = go 0 where
    lamPrec = 8
    appPrec = 9
    go i = \case
        Vi n -> shows n
        Vb b -> shows b
        Vv v -> showString v
        Lam t n exp -> 
            showParen (i >= lamPrec)
            $ showString "\\lambda " 
            . showString n 
            . showString " : " 
            . showLatexType t
            . showString " . "
            . go lamPrec exp
        App e1 e2 ->
            showParen (i >= appPrec)
            $ go appPrec e1
            . showString "\\ " 
            . go 0 e2

showLatexType :: Vtype -> ShowS
showLatexType = go 0 where
    arrPrec = 8
    go i = \case
        Tint -> showString "\\mathit{int}"
        Tbool -> showString "\\mathit{bool}"
        Tdyn -> showString "*"
        Tfun e1 e2 ->
            showParen (i >= arrPrec)
            $ go arrPrec e1
            . showString " \\to " 
            . go 0 e2