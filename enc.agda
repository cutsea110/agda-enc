open import Data.Fin hiding (_+_) renaming (zero to fzero; suc to fsuc)
open import Data.Nat

data List (`M : ℕ) : Fin (suc `M) → Set where
  ⟨⟩ : {A : Fin (suc `M)} → List `M A
  ⟨_⟩⌢_ : (A : Fin (suc `M)) → List `M A → List `M A
