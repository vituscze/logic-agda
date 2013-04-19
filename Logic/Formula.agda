module Logic.Formula where

open import Data.Empty
  using (⊥)
open import Data.List
  using (List; []; _∷_)
open import Data.Product
  using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; map; zip)
open import Data.Unit
  using (⊤; tt)
open import Function

open import Logic.Term
open import Logic.Formula.PrenexTree
  using (Q; all; ex; PrenexTree; add; nil; swapAll; toList)
  renaming (merge to merge-tree)

infix 5 _≤_

-- Defines what kind of quantifiers does a formula contain.
data Type : Set where
  none all both : Type

_≤_ : (t₁ t₂ : Type) → Set
none ≤ t₂   = ⊤
all  ≤ none = ⊥
all  ≤ t₂   = ⊤
both ≤ both = ⊤
both ≤ t₂   = ⊥

refl : ∀ t → t ≤ t
refl none = tt
refl all  = tt
refl both = tt

bothMax : ∀ t → t ≤ both
bothMax none = tt
bothMax all  = tt
bothMax both = tt

merge : (t₁ t₂ : Type) → Type
merge none t₂   = t₂
merge all  both = both
merge all  t₂   = all
merge both t₂   = both

mergeT : ∀ t₁ t₂ → t₁ ≤ t₂ → t₁ ≤ merge t₂ all
mergeT none t₂   = λ _ → tt
mergeT all  none = λ _ → tt
mergeT all  all  = λ _ → tt
mergeT all  both = λ _ → tt
mergeT both none = λ z → z
mergeT both all  = λ z → z
mergeT both both = λ _ → tt

data Prenex : Set where
  nope yep : Prenex

isPrenex : Prenex → Type → Prenex
isPrenex yep none = yep
isPrenex _   _    = nope

pBoth : Prenex → Prenex → Prenex
pBoth yep yep = yep
pBoth _   _   = nope

data Formula (R F V : Set) : Prenex → Type → Set where
  rel        : (r : R) (ts : List (Term F V))          → Formula R F V yep none
  all        : ∀ {p t} (x : V) (φ : Formula R F V p t) → Formula R F V p (merge t all)
  ex         : ∀ {p t} (x : V) (φ : Formula R F V p t) → Formula R F V p both
  not        : ∀ {p t}         (φ : Formula R F V p t) → Formula R F V (isPrenex p t) t
  and or imp : ∀ {p₁ p₂ t₁ t₂} (φ : Formula R F V p₁ t₁) (ψ : Formula R F V p₂ t₂) →
    let p = pBoth p₁ p₂
        t = merge  t₁ t₂
    in Formula R F V (isPrenex p t) t

prepend : ∀ {R F V p t₁} → List (Q V) → Formula R F V p t₁ → Σ[ t₂ ∈ Type ] (Formula R F V p t₂ × t₁ ≤ t₂)
prepend {t₁ = t}  []           φ = _ , φ , refl t
prepend           (q     ∷ qs) φ with prepend qs φ
prepend {t₁ = t′} (all x ∷ qs) φ | t , φ′ , pf = merge t all , all x φ′ , mergeT t′ t pf
prepend {t₁ = t′} (ex  x ∷ qs) φ | t , φ′ , pf = both        , ex  x φ′ , bothMax t′

remove : ∀ {R F V p t} → Formula R F V p t → Formula R F V yep none × PrenexTree V
remove (rel r ts) = rel r ts , nil
remove (all x φ)  = map id (add (all x)) (remove φ)
remove (ex  x φ)  = map id (add (ex  x)) (remove φ)
remove (not φ)    = map not swapAll    (remove φ)
remove (and φ ψ)  = zip and merge-tree (remove φ) (remove ψ)
remove (or  φ ψ)  = zip or  merge-tree (remove φ) (remove ψ)
remove (imp φ ψ)  = zip imp (merge-tree ∘ swapAll) (remove φ) (remove ψ)

