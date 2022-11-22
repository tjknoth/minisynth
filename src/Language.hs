{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}

module Language ( 
    Id
  , Hole (..)
  , Term (..)
  , Type (..)
  , TVar (..)
  , Environment (..)
  , Subst
  , Scheme (..)
  , Substitutable (..)
  , var, lam, ($$)
  , hole, spechole, filled
  , nullSubst, compose
  , initEnv
  , annotation
  , tint, tbool, tvar, (-->), tany
  , extend
  , occurs
  , arity
  , toMonotype
) where

import           Data.String (IsString (..))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set

type Id = String

data Hole = NoSpec | Spec Environment Type | Filled (Term Type)
  deriving (Eq, Ord, Show)

-- (Potentially annotated) program term
data Term a =
    Var a Id
  | App a (Term a) (Term a)
  | Lam a Id (Term a)
  | Hole a Hole
  deriving (Eq, Ord, Show, Functor)

var :: Id -> Term Type
var = Var TAny

instance IsString (Term Type) where
  fromString = var

($$) :: Term Type -> Term Type -> Term Type
f $$ x = App TAny f x

lam :: Id -> Term Type -> Term Type
lam = Lam TAny

hole :: Term Type
hole = Hole TAny NoSpec

spechole :: Environment -> Type -> Term Type
spechole e t = Hole TAny $ Spec e t

filled :: Term Type -> Term Type
filled = Hole TAny . Filled

-- Primitive type
data Prim = Int | Bool 
  deriving (Eq, Ord, Show)

newtype TVar = TV Id
  deriving (Eq, Ord, Show)

instance IsString TVar where
  fromString = TV

-- Type
data Type = 
    TPrim Prim
  | TVar TVar 
  | TArrow Type Type
  | TAny
  deriving (Eq, Ord, Show)

arity :: Type -> Int
arity (TArrow _ b) = 1 + arity b
arity _ = 0

instance IsString Type where
  fromString = TVar . TV

annotation :: Term a -> a
annotation (Var a _)   = a
annotation (App a _ _) = a
annotation (Lam a _ _) = a
annotation (Hole a _)  = a

tint, tbool :: Type
tint = TPrim Int
tbool = TPrim Bool

tvar :: Id -> Type
tvar = TVar . TV

(-->) :: Type -> Type -> Type
(-->) = TArrow

infixr 9 -->
infixl 9 $$

tany :: Type
tany = TAny

data Scheme = 
  Forall [TVar] Type
  deriving (Eq, Ord, Show)

toMonotype :: Scheme -> Type
toMonotype (Forall _ t) = t

data Environment = Env {
    vars :: Map Id Scheme
  , boundTVs :: Set TVar
  } deriving (Eq, Ord, Show)

initEnv :: Environment
initEnv = Env Map.empty Set.empty

extend :: Id -> Type -> Environment -> Environment
extend x t (Env e tvs) = Env (Map.insert x (Forall [] t) e) tvs

type Subst = Map TVar Type

nullSubst :: Subst
nullSubst = Map.empty

compose :: Subst -> Subst -> Subst
s1 `compose` s2 = Map.map (apply s1) s2 `Map.union` s1

class Substitutable a where
  apply :: Subst -> a -> a
  ftv :: a -> Set TVar

instance Substitutable Type where
  apply _ t@TPrim{}    = t
  apply s t@(TVar a)   = Map.findWithDefault t a s
  apply s (TArrow a b) = apply s a --> apply s b
  apply _ TAny = TAny
  ftv TPrim{}      = Set.empty
  ftv (TVar a)     = Set.singleton a
  ftv (TArrow a b) = ftv a `Set.union` ftv b
  ftv TAny         = Set.empty

instance Substitutable Scheme where
  apply s (Forall as t) = Forall as $ apply s' t
    where s' = foldr Map.delete s as
  ftv (Forall as t) = ftv t `Set.difference` Set.fromList as

instance Substitutable a => Substitutable [a] where
  apply = fmap . apply
  ftv   = foldr (Set.union . ftv) Set.empty

instance Substitutable a => Substitutable (a, a) where
  apply s (a, b) = (apply s a, apply s b) 
  ftv (a, b)     = Set.union (ftv a) (ftv b)

occurs :: Substitutable a => TVar -> a -> Bool
occurs a t = a `Set.member` ftv t