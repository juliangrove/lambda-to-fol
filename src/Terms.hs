{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Terms where

import Utterances
import qualified Formulae as FOL

-- | Typed λ-calculus, with monadic constructors

-- Types
data Type = E | T | I | U | R     -- Atomic types
          | Type :/\ Type -- Conjunctions
          | Unit          -- Tautology
          | Type :-> Type -- Implications
          | P Type        -- Probabilistic programs

-- Contexts
data Context = Empty | Cons Type Context

-- Ways of being in a context
data In (φ :: Type) (γ :: Context) where
  First :: In φ (Cons φ γ)
  Next :: In φ γ -> In φ (Cons ψ γ)
deriving instance Show (In φ γ)

-- Constants
data Constant (φ :: Type) where
  Dog :: Constant (E :-> T)
  Person :: Constant (E :-> T)
  Sleep :: Constant (E :-> T)
  -- SleepInt :: 
  -- Tall ::
  Teach :: Constant (E :-> (E :-> T))
  C :: Constant E
  J :: Constant E
  And :: Constant (T :-> (T :-> T))
  Or :: Constant (T :-> (T :-> T))
  Imp :: Constant (T :-> (T :-> T))
  Not :: Constant (T :-> T)
  Forall :: Constant ((E :-> T) :-> T)
  Exists :: Constant ((E :-> T) :-> T)
  Bernoulli :: Constant (R :-> P T)
  ToReal :: Double -> Constant R
  ToUtt :: Expr S -> Constant U
  ToWorld :: [FOL.Form] -> Constant I
  Interp :: Constant (U :-> (I :-> T))
  Factor :: Constant (R :-> P Unit)
  ExpVal :: Constant (P α :-> ((α :-> R) :-> R))
  Indi :: Constant (T :-> R)
  IfThenElse :: Constant (T :-> (α :-> (α :-> α)))
  DensityU :: Constant (P U :-> (U :-> R))
  DensityI :: Constant (P I :-> (I :-> R))
  Utterances :: Constant (P U)
  WorldKnowledge :: Constant (P I)
  Context :: Constant (P I)
  Alpha :: Constant (R :-> (R :-> R))
  Normal :: Constant (R :-> (R :-> P R))
deriving instance Show (Constant φ)

-- Typed λ-terms
data Term (γ :: Context) (φ :: Type) where
  Var :: In φ γ -> Term γ φ                        -- variables
  Con :: Constant φ -> Term γ φ                    -- constants
  Lam :: Term (Cons φ γ) ψ -> Term γ (φ :-> ψ)     -- abstraction
  App :: Term γ (φ :-> ψ) -> Term γ φ -> Term γ ψ  -- applications
  Pair :: Term γ φ -> Term γ ψ -> Term γ (φ :/\ ψ) -- pairing
  Pi1 :: Term γ (φ :/\ ψ) -> Term γ φ              -- first projection
  Pi2 :: Term γ (φ :/\ ψ) -> Term γ ψ              -- second projection
  Un :: Term γ Unit                                -- unit
  Let :: Term γ (P φ) -> Term (Cons φ γ) (P ψ) -> Term γ (P ψ) -- monadic bind
  Return :: Term γ φ -> Term γ (P φ)                           -- monadic return

-- General function allowing us to define ways of adjusting contexts
reorder :: forall γ δ ψ. (forall φ. In φ γ -> In φ δ) -> Term γ ψ -> Term δ ψ
reorder f (Var i) = Var (f i)
reorder _ (Con c) = Con c
reorder f (Lam t) = Lam (reorder g t)
  where g :: (forall χ. In χ (Cons φ γ) -> In χ (Cons φ δ))
        g First = First
        g (Next i) = Next (f i)
reorder f (App t u) = App (reorder f t) (reorder f u)
reorder f (Pair t u) = Pair (reorder f t) (reorder f u)
reorder f (Pi1 t) = Pi1 (reorder f t)
reorder f (Pi2 t) = Pi2 (reorder f t)
reorder _ Un = Un
reorder f (Return t) = Return (reorder f t)
reorder f (Let t u) = Let (reorder f t) (reorder g u)
  where g :: (forall χ. In χ (Cons φ γ) -> In χ (Cons φ δ))
        g First = First
        g (Next i) = Next (f i)

-- weaken, targetting the first position in the context
weaken :: Term γ φ -> Term (Cons ψ γ) φ
weaken = reorder Next

-- weaken, targeting the second position in the context
weaken2 :: Term (Cons φ γ) ψ -> Term (Cons φ (Cons χ γ)) ψ
weaken2 = reorder g
  where g :: In ψ (Cons φ γ) -> In ψ (Cons φ (Cons χ γ))
        g First = First
        g (Next i) = Next (Next i)

-- substitution
subst :: forall γ δ ψ. (forall φ. In φ γ -> Term δ φ) -> Term γ ψ -> Term δ ψ
subst f (Var i) = f i
subst f (Con c) = Con c
subst f (Lam t) = Lam (subst g t)
  where g :: forall φ χ. In φ (Cons χ γ) -> Term (Cons χ δ) φ
        g First = Var First
        g (Next i) = weaken (f i)
subst f (App t u) = App (subst f t) (subst f u)
subst f (Pair t u) = Pair (subst f t) (subst f u)
subst _ Un = Un
subst f (Return t) = Return (subst f t)
subst f (Let t u) = Let (subst f t) (subst g u)
  where g :: forall φ χ. In φ (Cons χ γ) -> Term (Cons χ δ) φ
        g First = Var First
        g (Next i) = weaken (f i)

-- substutite a term for the top variable in the context
subst0 :: forall γ φ ψ. Term γ φ -> Term (Cons φ γ) ψ -> Term γ ψ
subst0 t = subst f
  where f :: forall χ. In χ (Cons φ γ)-> Term γ χ
        f First = t
        f (Next i) = Var i

-- normal forms, now featuring monadic constructors!
normalForm :: Term γ φ -> Term γ φ
normalForm v@(Var _) = v                -- Variables are already in normal form.
normalForm c@(Con _) = c                -- So are constants.
normalForm (Lam t) = Lam (normalForm t) -- Abstractions are in normal form just in case their bodies are in normal form.
normalForm (App t u) =
  case normalForm t of
    Lam t' -> normalForm (subst0 (normalForm u) t') -- If the normal form of t is an abstraction, then we need to substitute and further normalize.
    t' -> App t' (normalForm u)                     -- Otherwise, we just need to take the normal form of the argument.
normalForm (Pair t u) = Pair (normalForm t) (normalForm u)
normalForm (Pi1 t) =
  case normalForm t of
    Pair u _ -> u
    t' -> Pi1 t'
normalForm (Pi2 t) =
  case normalForm t of
    Pair _ u -> u
    t' -> Pi2 t'
normalForm Un = Un
normalForm (Return t) = Return (normalForm t)
normalForm (Let t u) =
  case normalForm t of
    Return t' -> normalForm (subst0 t' (normalForm u))
    Let t' u' -> normalForm (Let t' (Let u' (weaken2 (normalForm u))))
    t' -> Let t' (normalForm u)
