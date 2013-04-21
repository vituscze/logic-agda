module Logic.Formula where

open import Category.Monad
  using (module RawMonad)
open import Coinduction
  using (♭)
open import Data.AVL
  using ()
open import Data.List
  using (List; []; _∷_; mapM)
open import Data.Maybe
  using (Maybe; maybe′)
open import Data.Product
  using (Σ; Σ-syntax; _×_; _,_; proj₁; map; zip)
open import Data.Stream
  using (Stream; _∷_)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Unit
  using (⊤; tt)
open import Function
  using (_∘_; id)
open import Level
  using ()
open import Relation.Binary
  using (Rel; IsStrictTotalOrder)
open import Relation.Binary.PropositionalEquality
  using (_≡_)

open import Category.Monad.RWS
  using ()
open import Logic.Term
open import Logic.Formula.PrenexTree
  using (Q; all; ex; PrenexTree; add; nil; swapAll; toList)
  renaming (merge to merge-tree)
open import Logic.Formula.Type

open Lemmas

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

  open Category.Monad.RWS Tree ⊤ (Stream V′) (λ _ _ → tt) tt
  open RawMonad monad

  RenameM : Set → Set
  RenameM = RWS

  getVar : RenameM V′
  getVar _ (x ∷ xs) = x , ♭ xs , tt

  localInsert : ∀ {A} → V → RenameM A → RenameM (V′ × A)
  localInsert v m = getVar >>= λ v′ → local (insert v v′) m >>= λ a → return (v′ , a)

  updateVar : V → RenameM (V ⊎ V′)
  updateVar v = maybe′ inj₂ (inj₁ v) ∘ lookup v <$> ask

  private
    module Dummy where
      renameT : ∀ {F} → Term F V → RenameM (Term F (V ⊎ V′))
      renameT     (var x)    = var   <$> updateVar x
      renameT {F} (fun f ts) = fun f <$> go ts
        where
          -- Help the termination checker a bit.
          go : List (Term F V) → RenameM (List (Term F (V ⊎ V′)))
          go []       = return []
          go (t ∷ ts) = _∷_ <$> renameT t ⊛ go ts

      rename : ∀ {R F t p} → Formula R F V t p → RenameM (Formula R F (V ⊎ V′) t p)
      rename (rel r ts) = rel r <$> mapM monad renameT ts
      rename (all x φ)  = all <$> updateVar x ⊛ rename φ
      rename (ex  x φ)  = ex  <$> updateVar x ⊛ rename φ
      rename (not φ)    = not <$> rename φ
      rename (and φ ψ)  = and <$> rename φ ⊛ rename ψ
      rename (or  φ ψ)  = or  <$> rename φ ⊛ rename ψ
      rename (imp φ ψ)  = imp <$> rename φ ⊛ rename ψ

  rename : ∀ {R F t p} → Stream V′ → Formula R F V t p → Formula R F (V ⊎ V′) t p
  rename vs f = proj₁ (Dummy.rename f empty vs)
