module Language ( 
    Id
  , Term (..)
  , Type (..)
  , Environment (..)
  , Subst
  , Scheme (..)
  , Substitutable (..)
  , annotation
  , tint, tbool, tvar, (-->)
  , extend
  , occurs
) where

import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set

type Id = String

-- (Potentially annotated) program term
data Term a =
    Var a Id
  | App a (Term a) (Term a)
  | Lam a Id (Term a)
  deriving (Eq, Ord, Show, Functor)

-- Primitive type
data Prim = Int | Bool 
  deriving (Eq, Ord, Show)

newtype TVar = TV Id
  deriving (Eq, Ord, Show)

-- Type
data Type = 
    TPrim Prim
  | TVar TVar 
  | TArrow Type Type
  deriving (Eq, Ord, Show)

annotation :: Term a -> a
annotation (Var a _) = a
annotation (App a _ _) = a
annotation (Lam a _ _) = a


tint, tbool :: Type
tint = TPrim Int
tbool = TPrim Bool

tvar :: Id -> Type
tvar = TVar . TV

(-->) :: Type -> Type -> Type
(-->) = TArrow

data Scheme = 
    Forall [TVar] Type

newtype Environment = Env (Map Id Scheme)

extend :: Id -> Type -> Environment -> Environment
extend x t (Env e) = Env $ Map.insert x (Forall [] t) e 

type Subst = Map TVar Type

class Substitutable a where
  apply :: Subst -> a -> a
  ftv :: a -> Set TVar

instance Substitutable Type where
  apply _ t@TPrim{}    = t
  apply s t@(TVar a)   = Map.findWithDefault t a s
  apply s (TArrow a b) = apply s a --> apply s b
  ftv TPrim{}      = Set.empty
  ftv (TVar a)     = Set.singleton a
  ftv (TArrow a b) = ftv a `Set.union` ftv b

instance Substitutable Scheme where
  apply s (Forall as t) = Forall as $ apply s' t
    where s' = foldr Map.delete s as
  ftv (Forall as t) = ftv t `Set.difference` Set.fromList as

instance Substitutable a => Substitutable [a] where
  apply = fmap . apply
  ftv   = foldr (Set.union . ftv) Set.empty

instance Substitutable Environment where
  apply s (Env env) = Env $ Map.map (apply s) env
  ftv (Env env) = ftv $ Map.elems env

occurs :: Substitutable a => TVar -> a -> Bool
occurs a t = a `Set.member` ftv t