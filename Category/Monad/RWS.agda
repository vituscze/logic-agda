module Category.Monad.RWS where

open import Category.Monad
  using (RawMonad)
open import Data.Product
  using (_×_; _,_)
open import Level
  using (_⊔_)
open import Relation.Binary.PropositionalEquality
  using (_≡_)
open import Data.Unit
  using (⊤; tt)

RWS : (R W S A : Set) → Set
RWS R W S A = R → S → A × S × W

-- Does not require IsMonoid for simplicity.
module RWSMonad (R W S : Set) (_∙_ : W → W → W) (ε : W) where

  monad : RawMonad (RWS R W S)
  monad = record
    { return = λ a r s → a , s , ε
    ; _>>=_  = λ m f r s →
        let a , s′ , w  = m r s
            b , s″ , w′ = f a r s′ 
        in b , s″ , w ∙ w′
    }

  ask : RWS R W S R
  ask r s = r , s , ε

  local : ∀ {A} → (R → R) → RWS R W S A → RWS R W S A
  local f m r s = m (f r) s

  get : RWS R W S S
  get r s = s , s , ε

  put : S → RWS R W S ⊤
  put s r _ = tt , s , ε

  tell : W → RWS R W S ⊤
  tell w r s = tt , s , w
