open import Data.Fin hiding (_+_)
open import Data.Nat

data List (M-1 : ℕ) : Fin (suc M-1) → Set where
