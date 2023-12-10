{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pretty where

import Terms

freshVars :: [String]
freshVars = concat (map (\s -> map (\c -> c:s) "xyzuvw") appendMe)
  where appendMe :: [String]
        appendMe = "" : map show ints

        ints :: [Integer]
        ints = 1 : map (\x -> x + 1) ints

printLambda :: forall γ ψ. [String] ->
               (forall φ. In φ γ -> String) ->
               Term γ ψ -> String
printLambda _ f (Var i) = f i
printLambda freshVs f (App t u) =
  "(" ++ printLambda freshVs f t ++ " " ++ printLambda freshVs f u ++ ")"
printLambda (fresh:vs) f (Lam t) =
  "(λ" ++ fresh ++ "." ++ printLambda vs f' t ++ ")"
  where f' :: forall φ χ. In φ (Cons χ γ) -> String
        f' First = fresh
        f' (Next i) = f i
printLambda _ _ (Con c) = show c
printLambda freshVs f (Pair t u) =
  "⟨" ++ printLambda freshVs f t ++ ", " ++ printLambda freshVs f u ++ "⟩"
printLambda _ _ Un = "⋄"
printLambda freshVs f (Pi1 t) = "(π₁ " ++ printLambda freshVs f t ++ ")"
printLambda freshVs f (Pi2 t) = "(π₂ " ++ printLambda freshVs f t ++ ")"
printLambda (fresh:vs) f (Let t u) =
  "(" ++ fresh ++ " ∼ " ++ printLambda vs f t ++ "; " ++
  printLambda vs f' u ++ ")"
    where f' :: forall φ χ. In φ (Cons χ γ) -> String
          f' First = fresh
          f' (Next i) = f i
printLambda freshVs f (Return t) = "[" ++ printLambda freshVs f t ++ "]"

instance Show (Term γ φ) where
  show t = printLambda freshVars (\case) t
