module Logic.Formula.PrenexTree where

open import Data.Bool
  using (Bool; true; false; not; _xor_)
open import Data.List
  using (List; []; _∷_; _++_; map)

open import Data.Nat

data Q (V : Set) : Set where
  all ex : V → Q V

data PrenexTree (V : Set) : Set where
  nil  : PrenexTree V
  node : (s : Bool) (qs : List (Q V)) (l r : PrenexTree V) → PrenexTree V 

swapWhen : ∀ {V} → Bool → Q V → Q V
swapWhen false = λ x → x
swapWhen true  = λ {(all x) → ex x; (ex x) → all x}

swapAll : ∀ {V} → PrenexTree V → PrenexTree V
swapAll nil             = nil
swapAll (node s qs l r) = node (not s) qs l r

add : ∀ {V} → Q V → PrenexTree V → PrenexTree V
add q nil             = node false (q ∷ []) nil nil
add q (node s qs l r) = node s (swapWhen s q ∷ qs) l r

merge : ∀ {V} (l r : PrenexTree V) → PrenexTree V
merge = node false []

toList : ∀ {V} → PrenexTree V → List (Q V)
toList {V} = go false
  where
    go : Bool → PrenexTree V → List (Q V)
    go p nil = []
    go p (node s qs l r) =
      let p′ = p xor s
      in map (swapWhen p′) qs ++ go p′ l ++ go p′ r
