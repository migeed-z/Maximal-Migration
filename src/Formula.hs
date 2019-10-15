{-# Language LambdaCase #-}
{-# Language DeriveDataTypeable #-}
module Formula where
import Data.Data
import Data.List as List
import Data.Map as Map
import Data.Set as Set

import Data.String

data Literal = Pos LiteralName
             | Neg LiteralName
             deriving (Eq, Data)

nameOfLiteral :: Literal -> LiteralName
nameOfLiteral = \case
    Pos a -> a
    Neg a -> a

newtype LiteralName = LiteralName String
    deriving (Eq, Data, Show)

instance IsString LiteralName where
    fromString = LiteralName

data Clause = Cl Literal Literal Literal
             deriving (Eq, Data)

type LFormula = [Clause]

literalNameAsString :: LiteralName -> String
literalNameAsString (LiteralName s) = s

nextLiteralName :: LiteralName -> LiteralName
nextLiteralName (LiteralName a) = LiteralName (a ++ "'")


pos :: String -> Literal
pos = Pos . LiteralName

neg :: String -> Literal
neg = Neg . LiteralName

instance Show Literal where
    showsPrec n = \case
        Pos (LiteralName a) -> showString a
        Neg (LiteralName a) -> (showString "¬").showString a 


instance Show Clause where
    showsPrec n = \case
        Cl a b c  -> showsPrec 0 a
                     . showString " ∨ "
                     . showsPrec 0 b 
                     . showString " ∨ "
                     . showsPrec 0 c




