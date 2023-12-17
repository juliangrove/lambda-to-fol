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
import Prelude hiding (Word)
import Pretty
import Terms
import Utterances

-- | Interpreting English expressions into λ-calculus

-- Each category has a corresponding semantic type.
type family SemType (c :: Cat) where
  SemType NP = E
  SemType N = E :-> T
  SemType S = T
  SemType (c1 :\: c2) = SemType c1 :-> SemType c2
  SemType (c2 :/: c1) = SemType c1 :-> SemType c2

-- Interpreting words
interpWord :: Word c -> Term Empty (((SemType c) :-> T) :-> T)
interpWord (Word "carina" IsAnNP) = Lam (App (Var First) (Con C))
interpWord (Word "everyone" IsAnNP) = Lam (App (Con Forall) (Var First))
interpWord (Word "someone" IsAnNP) = Lam (App (Con Exists) (Var First))
interpWord (Word "no one" IsAnNP) = Lam (App (Con Not) (App (Con Exists) (Var First)))
interpWord (Word "sleeps" (IsAnNP ::\:: IsAnS)) = Lam (App (Var First) (Con Sleep))
interpWord w = error $ show w

-- Interpreting expressions
interpExpr :: Expr c -> Term Empty (((SemType c) :-> T) :-> T)
interpExpr (Lex w) = interpWord w
interpExpr (AppL e1 e2) = Lam (App (weaken (interpExpr e1)) (Lam (App (weaken (weaken (interpExpr e2))) (Lam (App (Var (Next (Next First))) (App (Var First) (Var (Next First))))))))
interpExpr (AppR e1 e2) = Lam (App (weaken (interpExpr e1)) (Lam (App (weaken (weaken (interpExpr e2))) (Lam (App (Var (Next (Next First))) (App (Var (Next First)) (Var First)))))))

-- Lowering whole-sentence interpretations
lower :: Term γ ((T :-> T) :-> T) -> Term γ T
lower t = App t (Lam (Var First))

-- Taking an English sentence onto a λ-term of type T
interpS :: Expr S -> Term Empty T
interpS = lower . interpExpr

-- Taking an English sentence onto a first-order logic formula
englishToFOL :: Expr S -> FOL.Form
englishToFOL = interpClosedTerm . interpS

-- | Interpreting λ-calculus into Haskell

-- Probabilistic programs take projection functions and give back real numbers.
newtype ProbProg a = PP { unPP :: (a -> Double) -> Double }

instance Functor ProbProg where -- 'ProbProg' is a /Functor/.
  fmap f (PP m) = PP (\k -> m (k . f))

instance Applicative ProbProg where -- 'ProbProg' is /Applicative/.
  pure a = PP (\f -> f a)
  PP m <*> PP n = PP (\k -> m (\f -> n (\x -> k (f x))))

instance Monad ProbProg where -- 'ProbProg' is a /Monad/.
  PP m >>= k = PP (\f -> m (\x -> unPP (k x) f))

-- Each type has a corresponding domain.
type family Domain (φ :: Type) where
  Domain E = FOL.Term
  Domain T = FOL.Form
  Domain I = [FOL.Form]
  Domain U = Expr S
  Domain R = Double
  Domain (φ :-> ψ) = Domain φ -> Domain ψ
  Domain (φ :/\ ψ) = (Domain φ, Domain ψ)
  Domain Unit = ()
  Domain (P φ) = ProbProg (Domain φ)

-- Interpreting constants
interpCon :: Integer -> Constant φ -> Domain φ
interpCon _ C = FOL.N (FOL.Name 0)
interpCon _ J = FOL.N (FOL.Name 1)
interpCon _ (ToReal r) = r
interpCon _ (ToUtt u) = u
interpCon _ Bernoulli = \x -> bernoulli x -- see below
interpCon _ And = \p q -> FOL.And p q
interpCon _ Or = \p q -> FOL.Or p q
interpCon _ Imp = \p q -> FOL.Or (FOL.Not p) (FOL.Not q)
-- interpCon n Forall =
  -- \p -> FOL.Forall (FOL.Var n) (p (FOL.V (FOL.Var n)))
interpCon _ Forall = \p -> FOL.And (p (FOL.N (FOL.Name 0))) (p (FOL.N (FOL.Name 1)))
-- interpCon n Exists =
  -- \p -> FOL.Exists (FOL.Var n) (p (FOL.V (FOL.Var n)))
interpCon _ Exists = \p -> FOL.Or (p (FOL.N (FOL.Name 0))) (p (FOL.N (FOL.Name 1)))
interpCon _ Not = \p -> FOL.Not p
interpCon _ Sleep = sleep -- see below
interpCon _ Teach = teach -- see below
interpCon _ Indi = \φ -> indicator (entails 11 [] φ) -- see below; note that this this one goes to 3
interpCon _ ExpVal = expVal                          -- see below
interpCon _ Factor = factor                          -- see below
interpCon _ IfThenElse = \φ x y -> if entails 11 [] φ then x else y
interpCon _ Interp = \φ i -> if entails 11
                                (englishToFOL φ : i)
                                false
                             then false
                             else true
interpCon _ WorldKnowledge = worldKnowledge
interpCon _ Context = worldKnowledge
interpCon _ Utterances = utterances
interpCon _ DensityI = densityI
interpCon _ DensityU = densityU
interpCon _ Alpha = \x y -> y ** x
interpCon _ c = error $ show c

-- Interpreting λ-terms
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

-- For closed λ-terms encoding whole meanings
interpClosedTerm :: Term Empty φ -> Domain φ
interpClosedTerm = interpTerm 0 (\case)

-- Convenience functions in our metalanguage

categorical :: [Double] -> [a] -> ProbProg a
categorical ws vs = PP (\f -> sum (zipWith (*) ws (map f vs)))

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

p :: ProbProg Bool -> Double
p m = expVal m indicator

factor :: Double -> ProbProg ()
factor r = PP (\f -> r * f ())

-- Convenient λ-terms to have around:

prob :: Term γ (P T :-> R)
prob = Lam (App (App (Con ExpVal) (Var First)) (Con Indi))

true :: FOL.Form
true = FOL.Or (FOL.P 0 []) (FOL.Not (FOL.P 0 []))

false :: FOL.Form
false = FOL.And (FOL.P 0 []) (FOL.Not (FOL.P 0 []))

observe :: Term γ (T :-> P Unit)
observe = Lam (App (Con Factor) (App (Con Indi) (Var First)))

cOrJ :: Term γ (P E)
cOrJ = Let (App (Con Bernoulli) (Con (ToReal 0.8)))
       (Return (App (App (App (Con IfThenElse) (Var First)) (Con C)) (Con J)))

julianSlept = App (Con Sleep) (Con J)

worldKnowledge :: ProbProg [FOL.Form]
worldKnowledge = do f1 <- categorical [0.5, 0.5] [id, FOL.Not]
                    f2 <- categorical [0.5, 0.5] [id, FOL.Not]
                    pure [ f1 (sleep (FOL.N (FOL.Name 0)))
                         , f2 (sleep (FOL.N (FOL.Name 1))) ]

utterances :: ProbProg (Expr S)
utterances = categorical [0.33, 0.33, 0.33] [ everyoneSleeps
                                            , someoneSleeps
                                            , noOneSleeps ]

everyoneSleeps, someoneSleeps, noOneSleeps :: Expr S
everyoneSleeps = AppL (Lex (Word "everyone" IsAnNP)) (Lex (Word "sleeps" (IsAnNP ::\:: IsAnS)))
someoneSleeps = AppL (Lex (Word "someone" IsAnNP)) (Lex (Word "sleeps" (IsAnNP ::\:: IsAnS)))
noOneSleeps = AppL (Lex (Word "no one" IsAnNP)) (Lex (Word "sleeps" (IsAnNP ::\:: IsAnS)))


densityI :: ProbProg [FOL.Form] -> [FOL.Form] -> Double
densityI m i = expVal m (indicator . (mutualEntails 11 i))

mutualEntails :: Int -> [FOL.Form] -> [FOL.Form] -> Bool
mutualEntails n fs1 fs2 = all (entails n fs1) fs2 && all (entails n fs2) fs1

densityU :: ProbProg (Expr S) -> Expr S -> Double
densityU m u = expVal m (indicator . (== u))

-- >>> densityU utterances noOneSleeps
-- 0.33333333333333337

l :: Integer -> Term γ (U :-> P I)
l 0 = Lam (Let (Con Context) (Let (App (Con Factor) (App (Con Indi) (App (App (Con Interp) (Var (Next First))) (Var First)))) (Return (Var (Next First)))))
l i = Lam (Let (Con Context) (Let (App (Con Factor) (App (App (Con DensityU) (App (s i) (Var First))) (Var (Next First)))) (Return (Var (Next First)))))

s :: Integer -> Term γ (I :-> P U)
s i = Lam (Let (Con Utterances) (Let (App (Con Factor) (App (App (Con Alpha) (Con (ToReal 4))) (App (App (Con DensityI) (App (l (i-1)) (Var First))) (Var (Next First))))) (Return (Var (Next First)))))

-- >>> interpClosedTerm (App (Con DensityI) (App (l 0) (Con (ToUtt everyoneSleeps)))) i1
-- 1.0

example :: Term γ (P I)
example = Let (Con WorldKnowledge) (Let (App observe (App (App (Con Interp) (Con (ToUtt someoneSleeps))) (Var First))) (Return (Var (Next First))))

-- An example possible world
i0, i1 :: [FOL.Form]
i0 = [sleep (FOL.N (FOL.Name 1)), FOL.Not (sleep (FOL.N (FOL.Name 0)))]

i1 = [sleep (FOL.N (FOL.Name 1)), sleep (FOL.N (FOL.Name 0))]

-- >>>  interpClosedTerm (App (Con DensityI) (App (l 0) (Con (ToUtt someoneSleeps)))) i0
-- 0.3333333333333333

-- >>> p $ interpClosedTerm example >>= \i -> return (entails 11 i (sleep (FOL.N (FOL.Name 0))))
-- 0.6666666666666666
