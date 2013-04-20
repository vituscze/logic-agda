module Logic.Formula where

open import Category.Monad
open import Coinduction
open import Data.AVL
  using ()
open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.List
  using (List; []; _∷_; mapM)
open import Data.Maybe
  using (Maybe; maybe′)
open import Data.Product
  using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; map; zip)
open import Data.Stream
  using (Stream; _∷_)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Unit
  using (⊤; tt)
open import Function
open import Level
  using ()
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (refl to ≡-refl)

open import Category.Monad.RWS
open import Logic.Term
open import Logic.Formula.PrenexTree
  using (Q; all; ex; PrenexTree; add; nil; swapAll; toList)
  renaming (merge to merge-tree)

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

t-refl : ∀ t → t ≤t t
t-refl none = tt
t-refl all  = tt
t-refl both = tt

bothMax : ∀ t → t ≤t both
bothMax none = tt
bothMax all  = tt
bothMax both = tt

merge : (t₁ t₂ : Type) → Type
merge none t₂   = t₂
merge all  both = both
merge all  t₂   = all
merge both t₂   = both

merge-≤ : ∀ t₁ t₂ → t₁ ≤t t₂ → t₁ ≤t merge t₂ all
merge-≤ none t₂   = λ _ → tt
merge-≤ all  none = λ _ → tt
merge-≤ all  all  = λ _ → tt
merge-≤ all  both = λ _ → tt
merge-≤ both none = λ z → z
merge-≤ both all  = λ z → z
merge-≤ both both = λ _ → tt

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

prepend : ∀ {R F V p t₁} → List (Q V) → Formula R F V p t₁ → Σ[ t₂ ∈ Type ] (Formula R F V p t₂ × t₁ ≤t t₂)
prepend {t₁ = t}  []           φ = _ , φ , t-refl t
prepend           (q     ∷ qs) φ with prepend qs φ
prepend {t₁ = t′} (all x ∷ qs) φ | t , φ′ , pf = merge t all , all x φ′ , merge-≤ t′ t pf
prepend {t₁ = t′} (ex  x ∷ qs) φ | t , φ′ , pf = both        , ex  x φ′ , bothMax t′

remove : ∀ {R F V p t} → Formula R F V p t → Formula R F V yep none × PrenexTree V
remove (rel r ts) = rel r ts , nil
remove (all x φ)  = map id (add (all x)) (remove φ)
remove (ex  x φ)  = map id (add (ex  x)) (remove φ)
remove (not φ)    = map not swapAll    (remove φ)
remove (and φ ψ)  = zip and merge-tree (remove φ) (remove ψ)
remove (or  φ ψ)  = zip or  merge-tree (remove φ) (remove ψ)
remove (imp φ ψ)  = zip imp (merge-tree ∘ swapAll) (remove φ) (remove ψ)

module Rename
  {V V′ : Set} {_<_ : Rel V Level.zero}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

  open Data.AVL (λ _ → V′) isStrictTotalOrder

  open RWSMonad Tree ⊤ (Stream V′) (λ _ _ → tt) tt
  open RawMonad monad

  RenameM : Set → Set
  RenameM = RWS

  getVar : RenameM V′
  getVar _ (x ∷ xs) = x , ♭ xs , tt

  localInsert : ∀ {A} → V → RenameM A → RenameM (V′ × A)
  localInsert v m = getVar >>= λ v′ → local (insert v v′) m >>= λ a → return (v′ , a)

  updateVar : V → RenameM (V ⊎ V′)
  updateVar v = ask >>= λ t → return (maybe′ inj₂ (inj₁ v) (lookup v t))

  renameT : ∀ {F} → Term F V → RenameM (Term F (V ⊎ V′))
  renameT     (var x) = updateVar x >>= return ∘ var
  renameT {F} (fun f ts) = go ts >>= λ ts′ → return (fun f ts′)
    where
      -- Help the termination checker a bit.
      go : List (Term F V) → RenameM (List (Term F (V ⊎ V′)))
      go []       = return []
      go (t ∷ ts) = renameT t >>= λ t′ → go ts >>= λ ts′ → return (t′ ∷ ts′) 

  rename : ∀ {R F t p} → Formula R F V t p → RenameM (Formula R F (V ⊎ V′) t p)
  rename (rel r ts) = rel r <$> mapM monad renameT ts
  rename (all x φ)  = all <$> updateVar x ⊛ rename φ
  rename (ex  x φ)  = ex  <$> updateVar x ⊛ rename φ
  rename (not φ)    = not <$> rename φ
  rename (and φ ψ)  = and <$> rename φ ⊛ rename ψ
  rename (or  φ ψ)  = or  <$> rename φ ⊛ rename ψ
  rename (imp φ ψ)  = imp <$> rename φ ⊛ rename ψ
