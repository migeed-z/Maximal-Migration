
{-# Language QuasiQuotes #-}

module TH where

import Lang

import Language.Haskell.TH.Quote

import Text.Megaparsec
import Text.Megaparsec.Char

import Control.Monad.IO.Class
import Data.Void

type Parser = Parsec Void String

parseTerm :: Parser Expr
parseTerm = do
    t1 <- simpleTerm
    choice 
        [ do
            char ' '
            t2 <- parseTerm
            return (App t1 t2)
        , return t1
        ]

    where 
        simpleTerm = choice 
            [ char '(' *> space *> parseTerm <* space <* char ')'
            , do 
                i <- (char '\\' <|> char 'λ') *> pidentifier 
                space *> char ':' <* space
                t <- ptype
                space *> char '.' <* space
                term <- parseTerm
                return (Lam t i term)
            , try $ do 
                i <- many digitChar
                return $ Vi (read i)
            , string "True" *> pure (Vb True)
            , string "False" *> pure (Vb False)
            , Vv <$> pidentifier
           
            ]

ptype :: Parser Vtype
ptype = do
    t1 <- psimpletype
    choice 
        [ try $ do 
            space *> string "->" *> space
            t2 <- ptype
            return (t1 ~> t2)
        , do 
            return t1
        ]
    where
        psimpletype = choice
            [ string "int" *> return Tint
            , string "bool" *> return Tbool
            , char '*' *> return Tdyn
            , char '(' *> space *> ptype <* space <* char ')'
            ]

pidentifier :: Parser String
pidentifier = many alphaNumChar

prog = QuasiQuoter 
  { quoteExp = \str -> do 
    x <- case parse (parseTerm <* eof) str str of
        Right x -> return x
        Left y -> error (errorBundlePretty y)
    dataToExpQ (const Nothing) x
  , quotePat = undefined
  , quoteType = undefined
  , quoteDec = undefined
  }