{-# Language LambdaCase #-}
{-# Language DeriveDataTypeable #-}
{-# Language ViewPatterns #-}

module Constraint where

import Data.Data
import Data.Void
import Data.List as List
import Data.Map as Map
import Data.Set as Set
import Data.Maybe (fromJust)
import Data.Maybe (isJust)
import Control.Monad
import TypeCheck
import Lang


simple :: Either Void a -> a
simple (Left x) = absurd x
simple (Right y) = y


data CType 
  = CVar Int 
  | CArr CType CType
  | CInt
  | CDyn
  | CBool
  deriving (Eq, Data)
 

infixr 7 .~>
(.~>) = CArr

data Constraint 
  = Matching CType CType 
  | Equality CType CType
  | Consistency CType CType
  | Precision CType CType
  deriving (Eq, Data)

(.~) = Consistency
(.=) = Equality
(.|>) = Matching
(.<=) = Precision


instance Show CType where
    showsPrec n = \case
        CInt  -> showString "int"
        CBool -> showString "bool" 
        CDyn -> showChar '*'  
        CVar n -> shows n
        CArr a b -> showParen (n > fun_prec) (
            showsPrec (fun_prec + 1) a 
            . showString " -> " 
            . showsPrec fun_prec b
            )
        where fun_prec = 9   

--printer
instance Show Constraint where
    showsPrec n = \case
        Equality t1 t2 -> showsPrec 0 t1 .
                          showString " = " . 
                          showsPrec 0 t2

        Matching t1 t2 -> showsPrec 0 t1 .
                          showString " |> " . 
                          showsPrec 0 t2

        Precision t1 t2 -> showsPrec 0 t1 .
                          showString " <= " . 
                          showsPrec 0 t2

        Consistency t1 t2 -> showsPrec 0 t1 .
                          showString " ~ " . 
                          showsPrec 0 t2

-- vToCType (fromJust (envlookup x env)))


newtype State s a = State { runState :: s -> (s, a) }


instance Functor (State s) where
  fmap f ma = State 
    (\s -> let (s', a) = runState ma s in (s', f a))


instance Applicative (State s) where
  pure a = State (\s -> (s, a))
  (<*>) = ap

instance Monad (State s) where
  return a = State (\s -> (s, a))

  ma >>= amb = State $ \s -> 
    let (s', a) = runState ma s
    in runState (amb a) s'


gen = State (\cid -> (cid + 1, CVar cid))

vToCType :: Vtype -> CType
vToCType = \case 
  Tint -> CInt
  Tbool -> CBool
  Tdyn -> CDyn
  Tfun t1 t2 -> CArr (vToCType t1) (vToCType t2) 


--constraint generator
constraint :: Expr -> Env -> (CType, [Constraint])
constraint t senv  = snd $ runState (go t []) 0 where

  go ::  Expr -> [(String, CType)] -> State Int (CType, [Constraint])

  go t env = do 
    v <- gen 
    cs <- case t of
      Vi n -> do
        return [v .= CInt]

      Vb b -> do
        return [v .= CBool]

      Vv x -> case List.lookup x env of 
        Nothing -> do
          return [v .= vToCType (fromJust (envlookup x senv))]
        Just xid -> do
          return [v .= xid]

      Lam s x f -> do
        xid <- gen
        (fid, cs) <- go f ((x, xid):env) 
        return ([ v .= CArr xid fid, vToCType s .<= xid ] ++ cs)

      App f g -> do 
        (fid, fcs) <- go f env 
        (gid, gcs) <- go g env 
        gid' <- gen 
        return ([ fid .|> (CArr gid' v), gid' .~ gid] ++ fcs ++ gcs)

        
    return (v, cs)



