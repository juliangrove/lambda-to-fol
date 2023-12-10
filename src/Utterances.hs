{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Utterances where

import Prelude hiding (Word)

-- | Applicative categorial grammar

data Cat = NP | N | S
         | Cat :\: Cat
         | Cat :/: Cat

data Word (c :: Cat) = Word String (IsA c)

data IsA (c :: Cat) where
  IsAnNP :: IsA NP
  IsAnN :: IsA N
  IsAnS :: IsA S
  (::\::) :: IsA c1 -> IsA c2 -> IsA (c1 :\: c2)
  (::/::) :: IsA c1 -> IsA c2 -> IsA (c1 :/: c2)

instance Show (IsA c) where
  show IsAnNP = "np"
  show IsAnN = "n"
  show IsAnS = "s"
  show (c1 ::\:: c2) = "(" ++ show c1 ++ "\\" ++ show c2 ++ ")"
  show (c1 ::/:: c2) = "(" ++ show c1 ++ "/" ++ show c2 ++ ")"

instance Show (Word c) where
  show (Word s c) = "(" ++ s ++ " ⊢ " ++ show c ++ ")"

data Expr (c :: Cat) where
  Lex :: Word c -> Expr c
  AppL :: Expr c1 -> Expr (c1 :\: c2) -> Expr c2
  AppR :: Expr (c2 :/: c1) -> Expr c1 -> Expr c2

compareIsA :: IsA c1 -> IsA c2 -> Maybe Bool
compareIsA IsAnNP IsAnNP = Just True
compareIsA IsAnN IsAnN = Just True
compareIsA IsAnS IsAnS = Just True
compareIsA (c1 ::\:: c2) (c3 ::\:: c4) =
  do b1 <- compareIsA c1 c3
     b2 <- compareIsA c2 c4
     pure (b1 && b2)
compareIsA (c1 ::/:: c2) (c3 ::/:: c4) =
  do b1 <- compareIsA c1 c3
     b2 <- compareIsA c2 c4
     pure (b1 && b2)
compareIsA _ _ = Nothing

compareWord :: Word c1 -> Word c2 -> Maybe Bool
compareWord (Word s1 c1) (Word s2 c2) =
  do b <- compareIsA c1 c2
     pure (b && s1 == s2)

compareExpr :: Expr c1 -> Expr c2 -> Maybe Bool
compareExpr (Lex w1) (Lex w2) = compareWord w1 w2
compareExpr (AppL e1 e2) (AppL e3 e4) =
  do b1 <- compareExpr e1 e3
     b2 <- compareExpr e2 e4
     pure (b1 && b2)
compareExpr (AppR e1 e2) (AppR e3 e4) =
  do b1 <- compareExpr e1 e3
     b2 <- compareExpr e2 e4
     pure (b1 && b2)
compareExpr _ _ = Nothing

instance Eq (Expr c) where
  e1 == e2 = case compareExpr e1 e2 of
               Just True -> True
               _ -> False

instance Show (Expr c) where
  show (Lex w) = show w
  show (AppL e1 e2) = "(" ++ show e1 ++ " ◃ " ++ show e2 ++ ")"
  show (AppR e1 e2) = "(" ++ show e1 ++ " ▹ " ++ show e2 ++ ")"

-- | Some expressions

julianSlept :: Expr S
julianSlept = (AppL (Lex (Word "julian" IsAnNP)) (Lex (Word "slept" (IsAnNP ::\:: IsAnS))))

julianIsAPerson :: Expr S
julianIsAPerson = (AppL (Lex (Word "julian" IsAnNP)) (Lex (Word "is a person" (IsAnNP ::\:: IsAnS))))

carinaIsAPerson :: Expr S
carinaIsAPerson = (AppL (Lex (Word "carina" IsAnNP)) (Lex (Word "is a person" (IsAnNP ::\:: IsAnS))))

someoneSlept :: Expr S
someoneSlept = (AppL (Lex (Word "someone" IsAnNP)) (Lex (Word "slept" (IsAnNP ::\:: IsAnS))))

julianTaughtCarina :: Expr S
julianTaughtCarina = (AppL (Lex (Word "julian" IsAnNP)) (AppR (Lex (Word "taught" ((IsAnNP ::\:: IsAnS) ::/:: IsAnNP))) (Lex (Word "carina" IsAnNP))))

someoneTaughtSomeone :: Expr S
someoneTaughtSomeone = (AppL (Lex (Word "someone" IsAnNP)) (AppR (Lex (Word "taught" ((IsAnNP ::\:: IsAnS) ::/:: IsAnNP))) (Lex (Word "someone" IsAnNP))))
