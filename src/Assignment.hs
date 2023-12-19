{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Assignment where

import Convenience (entails)
import qualified Formulae as FOL 
import LambdaToFOL(observe
                  , true
                  , false
                  , sleep
                  , teach
                  , everyoneSleeps
                  , someoneSleeps
                  , noOneSleeps
                  , mutualEntails
                  , indicator
                  , l
                  , s
                  , i0
                  , i1
                  , i2)
import qualified LambdaToFOL as LTFOL
import Prelude hiding (Word)
import Pretty
import qualified ProbProg.Gibbs as ProbProg
import ProbProg.Logits
import ProbProg.Histograms
import ProbProg.PreciseProb
import ProbProg.ProbLang(Distribution(..)
                        , factor
                        , Probabilistic
                        , sample)
import Terms
import Utterances

-- | Some convenience functions

normal :: Probabilistic Double ->
          Probabilistic Double ->
          ProbProg.P (Probabilistic Double)
normal mu sigma = sample (Gaussian mu sigma)

bernoulli :: Probabilistic Double -> ProbProg.P (Probabilistic Bool)
bernoulli p = sample (ProbProg.ProbLang.Bernoulli p)

compatible :: [FOL.Form] -> FOL.Form -> Bool
compatible i φ = not (entails 11 (φ:i) false)

context :: ProbProg.P (Probabilistic ([FOL.Form], Double))
context = do d <- normal (pure 68) (pure 3)
             tau1 <- bernoulli (pure 0.5)
             tau2 <- bernoulli (pure 0.5)
             let ite = (\b -> if b then FOL.Not else id)
                 f1 = ite <$> tau1
                 f2 = ite <$> tau2
                 fs = (\f1 f2 -> [ f1 (sleep (FOL.N (FOL.Name 0)))
                                 , f2 (sleep (FOL.N (FOL.Name 1))) ]) <$>
                      f1 <*> f2
                 i = (,) <$> fs <*> d
             return i

utterances :: ProbProg.P (Probabilistic (Expr S))
utterances = do tau1 <- bernoulli (pure (1/3))
                tau2 <- bernoulli (pure 0.5)
                let choose = (\b0 b1 -> if b0
                                        then everyoneSleeps
                                        else if b1
                                             then someoneSleeps
                                             else noOneSleeps)
                    choice = choose <$> tau1 <*> tau2
                return choice

height :: FOL.Term -> Double
height (FOL.N (FOL.Name 0)) = 68
height (FOL.N (FOL.Name 1)) = 68

-- carinaIsTall :: Expr S
-- carinaIsTall =

-- julianIsTall :: Expr S
-- julianIsTall =


-- | Interpreting English expressions into λ-calculus

-- Each category has a corresponding semantic type.
-- type family SemType (c :: Cat) where
  -- SemType NP =
  -- SemType N =
  -- SemType S =
  -- SemType (c1 :\: c2) =
  -- SemType (c2 :/: c1) =

-- Interpreting words
-- interpWord :: Word c -> Term Empty (((SemType c) :-> (I :-> T)) :-> (I :-> T))
-- interpWord (Word "carina" IsAnNP) = Lam (App (Var First) (Con C))
-- interpWord (Word "julian" IsAnNP) = Lam (App (Var First) (Con J))
-- interpWord (Word "everyone" IsAnNP) =
--   Lam (Lam (App (Con Forall) (Lam (App (App (Var (Next (Next First))) (Var First)) (Var (Next First))))))
-- interpWord (Word "someone" IsAnNP) =
--   Lam (Lam (App (Con Exists) (Lam (App (App (Var (Next (Next First))) (Var First)) (Var (Next First))))))
-- interpWord (Word "no one" IsAnNP) =
--   Lam (Lam (App (Con Not) (App (Con Exists) (Lam (App (App (Var (Next (Next First))) (Var First)) (Var (Next First)))))))
-- interpWord (Word "sleeps" (IsAnNP ::\:: IsAnS)) = 
-- interpWord (Word "is tall" (IsAnNP ::\:: IsAnS)) = 
-- interpWord w = error $ show w

-- Interpreting expressions
-- interpExpr :: Expr c -> Term Empty (((SemType c) :-> (I :-> T)) :-> (I :-> T))
-- interpExpr (Lex w) = interpWord w
-- interpExpr (AppL e1 e2) = Lam (App (weaken (interpExpr e1)) (Lam (App (weaken (weaken (interpExpr e2))) (Lam (App (Var (Next (Next First))) (App (Var First) (Var (Next First))))))))
-- interpExpr (AppR e1 e2) = Lam (App (weaken (interpExpr e1)) (Lam (App (weaken (weaken (interpExpr e2))) (Lam (App (Var (Next (Next First))) (App (Var (Next First)) (Var First)))))))

-- Lowering whole-sentence interpretations
-- lower :: Term γ (((I :-> T) :-> (I :-> T)) :-> (I :-> T)) -> Term γ (I :-> T)
-- lower t =  

-- Taking an English sentence onto a λ-term of type T
-- interpS :: Expr S -> Term Empty (I :-> T)
-- interpS = lower . interpExpr

-- Taking an English sentence onto a function from worlds to first-order logic
-- formulae
-- englishToFOL :: Expr S -> ([FOL.Form], Double) -> FOL.Form
-- englishToFOL = interpClosedTermNL . interpS
              
-- | Interpretation

-- A domain for each type. Note that probabilistic programs are now interpreted
-- via the importanted Monte Carlo DSL.
type family Domain (φ :: Type) where
  Domain E = Probabilistic (FOL.Term)
  Domain T = Probabilistic (FOL.Form)
--   Domain I = Probabilistic _
  Domain U = Probabilistic (Expr S)
  Domain R = Probabilistic (Double)
  Domain (φ :-> ψ) = Domain φ -> Domain ψ
  Domain (φ :/\ ψ) = (Domain φ, Domain ψ)
  Domain Unit = ()
  Domain (P φ) = ProbProg.P (Domain φ)

-- A domain for each semantic type of a natural language expression.
type family DomainNL (φ :: Type) where
  DomainNL E = FOL.Term
  DomainNL T = FOL.Form
  -- DomainNL I = 
  DomainNL U = Expr S
  DomainNL R = Double
  DomainNL (φ :-> ψ) = DomainNL φ -> DomainNL ψ
  DomainNL (φ :/\ ψ) = (DomainNL φ, DomainNL ψ)
  DomainNL Unit = ()

-- interpConNL :: Constant φ -> DomainNL φ
-- interpConNL C = FOL.N (FOL.Name 0)
-- interpConNL J = FOL.N (FOL.Name 1)
-- interpConNL (ToReal r) = r
-- interpConNL (ToUtt u) = u
-- interpConNL And = \p q -> FOL.And p q
-- interpConNL Or = \p q -> FOL.Or p q
-- interpConNL Imp = \p q -> FOL.Or (FOL.Not p) (FOL.Not q)
-- interpConNL Forall = \p -> FOL.And (p (FOL.N (FOL.Name 0))) (p (FOL.N (FOL.Name 1)))
-- interpConNL Exists = \p -> FOL.Or (p (FOL.N (FOL.Name 0))) (p (FOL.N (FOL.Name 1)))
-- interpConNL Not = \p -> FOL.Not p
-- interpConNL Sleep = sleep
-- interpConNL Teach = teach
-- interpConNL SleepInt = sleepInt
--   where sleepInt :: FOL.Term -> ([FOL.Form], Double) -> FOL.Form
--         sleepInt x (fs, _) = if compatible fs (sleep x) then true else false
-- interpConNL Tall = tall
--   where tall :: FOL.Term -> ([FOL.Form], Double) -> FOL.Form
--                                                                -- Write your definition of @tall@ on this line.

-- interpTermNL :: (forall φ.In φ γ -> DomainNL φ) -> Term γ ψ -> DomainNL ψ
-- interpTermNL _ (Con c) = interpConNL c
-- interpTermNL g (Var v) = g v
-- interpTermNL g (App t u) = interpTermNL g t (interpTermNL g u)
-- interpTermNL g (Lam t) =
--   \x -> interpTermNL (\i -> case i of First -> x; Next j -> g j) t

-- For closed λ-terms encoding whole meanings of natural language expressions
-- interpClosedTermNL :: Term Empty φ -> DomainNL φ
-- interpClosedTermNL = interpTermNL (\case)

-- Interpreting constants
-- interpCon :: Constant φ -> Domain φ
-- interpCon C = pure (FOL.N (FOL.Name 0))
-- interpCon J = pure (FOL.N (FOL.Name 1))
-- interpCon (ToReal r) = pure r
-- interpCon (ToUtt u) = pure u
-- interpCon And = \p q -> FOL.And <$> p <*> q
-- interpCon Or = \p q -> FOL.Or <$> p <*> q
-- interpCon Imp = \p q -> FOL.Or <$> (FOL.Not <$> p) <*> (FOL.Not <$> q)
-- interpCon Forall = \f -> FOL.And <$>
--                          (f (pure (FOL.N (FOL.Name 0)))) <*>
--                          (f (pure (FOL.N (FOL.Name 1))))
-- interpCon Exists = \f -> FOL.Or <$>
--                          (f (pure (FOL.N (FOL.Name 0)))) <*>
--                          (f (pure (FOL.N (FOL.Name 1))))
-- interpCon Not = \p -> FOL.Not <$> p
-- interpCon Factor = factor . fmap toLogit
-- interpCon Terms.Bernoulli =
--   \r -> do b <- bernoulli r
--            let ite = (\b' -> if b' then true else false)
--            return (ite <$> b)
-- interpCon Normal = normal
-- interpCon SleepInt = \x i -> sleepInt <$> x <*> i
--   where sleepInt :: FOL.Term -> ([FOL.Form], Double) -> FOL.Form
--         sleepInt x (fs, _) = if compatible fs (sleep x) then true else false
-- interpCon Tall = \x i -> tall <$> x <*> i
--   where tall :: FOL.Term -> ([FOL.Form], Double) -> FOL.Form
--         tall x (_, d) = if height x >= d then true else false
-- interpCon Interp = \e i -> englishToFOL <$> e <*> i
-- interpCon Context = context
-- interpCon Utterances = utterances
-- interpCon Alpha = \x y -> (**) <$> x <*> y
-- interpCon DensityI = \m i -> ProbProg.probabilityWithN 100000 (fmap (\i' -> (\(fs, d) (fs', d') -> mutualEntails 11 fs fs' && d <= d' + 10 && d >= d' - 10) <$> i <*> i') m)
-- interpCon DensityU = \m u -> ProbProg.probabilityWithN 100000 (fmap ((==) <$> u <*>) m)
-- interpCon Indi = \φ -> (indicator . entails 11 []) <$> φ
-- interpCon t = error (show t)

-- Interpreting λ-terms
-- This is the idea for our monadic contructors:
-- >>> ⟦return a⟧ f = f ⟦a⟧
-- >>> ⟦let t u⟧ f = ⟦t⟧ (λx.⟦u⟧ˣ f)
-- interpTerm :: (forall φ.In φ γ -> Domain φ) -> Term γ ψ -> Domain ψ
-- interpTerm _ (Con c) = interpCon c
-- interpTerm g (Var v) = g v
-- interpTerm g (App t u) = interpTerm g t (interpTerm g u)
-- interpTerm g (Lam t) =
--   \x -> interpTerm (\i -> case i of First -> x; Next j -> g j) t
-- interpTerm g (Return t) = return (interpTerm g t)
-- interpTerm g (Let t u) =
--   interpTerm g t >>= \x ->
--                        interpTerm (\i -> case i of First -> x; Next j -> g j) u

-- For closed λ-terms encoding whole meanings
-- interpClosedTerm :: Term Empty φ -> Domain φ
-- interpClosedTerm = interpTerm (\case)

-- exercise8 :: Term γ (P I)
-- exercise8 = 

-- exercise9 :: Term γ (P T)
-- exercise9 =

-- exercise10 :: Probabilistic Double
-- exercise10 = ProbProg.probabilityWithN 100000 (fmap (fmap (entails 11 [])) (interpClosedTerm exercise9))
