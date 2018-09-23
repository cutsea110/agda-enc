open import Data.Fin hiding (_+_) renaming (zero to fzero; suc to fsuc)
open import Data.Nat

data List (`M : ℕ) (A : Fin (suc `M)) : Set where
  ⟨⟩ : List `M A
  ⟨_⟩⌢_ : Fin (suc `M) → List `M A → List `M A


data enc (`M : ℕ){A : Fin (suc `M)} : List `M A → Set where
  nil  : enc `M ⟨⟩
  cons : (x : Fin (suc `M)) → (s : List `M A) → enc `M (⟨ x ⟩⌢ s)
