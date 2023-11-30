{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module LambdaToFOL where

import Convenience (entails)
import qualified Formulae as FOL
import Terms

-- probabilistic programs take projection functions and give back real numbers
newtype ProbProg a = PP { unPP :: (a -> Double) -> Double }

instance Functor ProbProg where -- 'ProbProg' is a /Functor/.
  fmap f (PP m) = PP (\k -> m (k . f))

instance Applicative ProbProg where -- 'ProbProg' is /Applicative/.
  pure a = PP (\f -> f a)
  PP m <*> PP n = PP (\k -> m (\f -> n (\x -> k (f x))))

instance Monad ProbProg where -- 'ProbProg' is a /Monad/.
  PP m >>= k = PP (\f -> m (\x -> unPP (k x) f))

type family Domain (φ :: Type) where
  Domain E = FOL.Term
  Domain T = FOL.Form
  Domain R = Double
  Domain (φ :-> ψ) = Domain φ -> Domain ψ
  Domain (φ :/\ ψ) = (Domain φ, Domain ψ)
  Domain (P φ) = ProbProg (Domain φ)

-- Interpreting constants
interpCon :: Integer -> Constant φ -> Domain φ
interpCon _ C = FOL.N (FOL.Name 0)
interpCon _ J = FOL.N (FOL.Name 1)
interpCon _ (ToReal r) = r
interpCon _ Bernoulli = \x -> bernoulli x -- see below
interpCon _ And = \p q -> FOL.And p q
interpCon _ Or = \p q -> FOL.Or p q
interpCon _ Imp = \p q -> FOL.Or (FOL.Not p) (FOL.Not q)
interpCon n Forall =
  \p -> FOL.Forall (FOL.Var n) (p (FOL.V (FOL.Var n)))
interpCon _ Not = \p -> FOL.Not p
interpCon _ Sleep = sleep -- see below
interpCon _ Teach = teach -- see below
interpCon _ Indi = \φ -> indicator (entails 11 [] φ) -- see below; note that this this one goes to 11
interpCon _ ExpVal = expVal                          -- see below

true :: FOL.Form
true = FOL.Or (FOL.P 0 []) (FOL.Not (FOL.P 0 []))

false :: FOL.Form
false = FOL.And (FOL.P 0 []) (FOL.Not (FOL.P 0 []))

-- Interpreting lambda-terms
-- Thie is the idea for our monadic contructors:
-- >>> ⟦return a⟧ f = f ⟦a⟧
-- >>> ⟦let t u⟧ f = ⟦t⟧ (λx.⟦u⟧ˣ f)
interpTerm :: Integer -> (forall φ.In φ γ -> Domain φ) -> Term γ ψ -> Domain ψ
interpTerm n _ (Con c) = interpCon n c
interpTerm _ g (Var v) = g v
interpTerm n g (App t u) = interpTerm (succ n) g t (interpTerm (succ n) g u)
interpTerm n g (Lam t) =
  \x -> interpTerm n (\i -> case i of First -> x; Next j -> g j) t
interpTerm n g (Return t) = return (interpTerm n g t)
interpTerm n g (Let t u) =
  interpTerm n g t >>= \x -> interpTerm n (\i -> case i of First -> x; Next j -> g j) u

-- For closed lambda-terms:
interpClosedTerm :: Term Empty φ -> Domain φ
interpClosedTerm = interpTerm 0 (\case)

-- Convenience functions in our metalanguage:

categorical :: [Double] -> [a] -> ProbProg a
categorical rs xs = PP (\f -> sum (zipWith (\r x -> r * f x) rs xs))

bernoulli :: Double -> ProbProg FOL.Form
bernoulli r = categorical [r, (1 - r)] [true, false]

carinaOrJulian :: ProbProg FOL.Term
carinaOrJulian = categorical [1, 2] [FOL.N (FOL.Name 0), FOL.N (FOL.Name 1)]

teach :: FOL.Term -> FOL.Term -> FOL.Form
teach = \x y -> FOL.P 2 [x, y]

sleep :: FOL.Term -> FOL.Form
sleep = \x -> FOL.P 1 [x]

mass :: ProbProg a -> Double
mass (PP m) = m (const 1)

indicator :: Bool -> Double
indicator b = if b then 1 else 0

probability :: Term γ (P T :-> R)
probability = Lam (App (App (Con ExpVal) (Var First)) (Con Indi))

expVal :: ProbProg a -> (a -> Double) -> Double
expVal (PP m) f = m f / m (const 1)


-- Convenient lambda-terms:

prob :: Term γ (P T :-> R)
prob = Lam (App (App (Con ExpVal) (Var First)) (Con Indi))
