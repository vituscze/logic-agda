-- Does not require IsMonoid for simplicity.
module Category.Monad.RWS
  (R W S : Set) (_∙_ : W → W → W) (ε : W)
  where

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

RWS : Set → Set
RWS A = R → S → A × S × W

monad : RawMonad RWS
monad = record
  { return = λ a r s → a , s , ε
  ; _>>=_  = λ m f r s →
      let a , s′ , w  = m r s
          b , s″ , w′ = f a r s′ 
      in b , s″ , w ∙ w′
  }

ask : RWS R
ask r s = r , s , ε

local : ∀ {A} → (R → R) → RWS A → RWS A
local f m r s = m (f r) s

get : RWS S
get r s = s , s , ε

put : S → RWS ⊤
put s r _ = tt , s , ε

tell : W → RWS ⊤
tell w r s = tt , s , w
