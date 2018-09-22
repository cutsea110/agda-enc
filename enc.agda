open import Data.Fin
open import Data.List renaming ([] to ⟨⟩; _++_ to _⌢_)
open import Data.Nat

data enc : (M : ℕ) → {M>0 : M > 0} → List (Fin M) → Set where
