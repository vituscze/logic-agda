module Logic.Formula.Type where

open import Data.Empty
  using (⊥)
open import Data.Unit
  using (⊤; tt)

infix 5 _≤t_

-- Defines what kind of quantifiers does a formula contain.
data Type : Set where
  none all both : Type

_≤t_ : (t₁ t₂ : Type) → Set
none ≤t t₂   = ⊤
all  ≤t none = ⊥
all  ≤t t₂   = ⊤
both ≤t both = ⊤
both ≤t t₂   = ⊥

merge : (t₁ t₂ : Type) → Type
merge none t₂   = t₂
merge all  both = both
merge all  t₂   = all
merge both t₂   = both

data Prenex : Set where
  nope yep : Prenex

isPrenex : Prenex → Type → Prenex
isPrenex yep none = yep
isPrenex _   _    = nope

pBoth : Prenex → Prenex → Prenex
pBoth yep yep = yep
pBoth _   _   = nope

module Lemmas where
  t-refl : ∀ t → t ≤t t
  t-refl none = tt
  t-refl all  = tt
  t-refl both = tt

  bothMax : ∀ t → t ≤t both
  bothMax none = tt
  bothMax all  = tt
  bothMax both = tt

  merge-≤ : ∀ t₁ t₂ → t₁ ≤t t₂ → t₁ ≤t merge t₂ all
  merge-≤ none t₂   = λ _ → tt
  merge-≤ all  none = λ _ → tt
  merge-≤ all  all  = λ _ → tt
  merge-≤ all  both = λ _ → tt
  merge-≤ both none = λ p → p
  merge-≤ both all  = λ p → p
  merge-≤ both both = λ _ → tt
