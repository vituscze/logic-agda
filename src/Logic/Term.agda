module Logic.Term where

open import Data.List

data Term (F V : Set) : Set where
  var : V → Term F V
  fun : F → List (Term F V) → Term F V