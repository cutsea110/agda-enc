open import Data.Fin hiding (_+_) renaming (zero to fzero; suc to fsuc)
open import Data.Nat
open import Relation.Binary.PropositionalEquality as PropEq

data List (`M : ℕ) (A : Fin (suc `M)) : Set where
  ⟨⟩ : List `M A
  ⟨_⟩⌢_ : Fin (suc `M) → List `M A → List `M A


data Enc (`M : ℕ){A : Fin (suc `M)} : List `M A → Set where
  nil  : Enc `M ⟨⟩
  cons : (x : Fin (suc `M)) → (s : List `M A) → Enc `M (⟨ x ⟩⌢ s)

enc : (`M : ℕ) {A : Fin (suc `M)} → List `M A → ℕ
enc `M ⟨⟩ = 0
enc `M (⟨ x ⟩⌢ s) = 1 + toℕ x + suc `M * enc `M s

dec : (`M : ℕ) {A : Fin (suc `M)} → ℕ → List `M A
dec `M zero = ⟨⟩
dec `M (suc n) = {!!}

law1 : {`M : ℕ}{A : Fin (suc `M)}{s : List `M A} → dec `M (enc `M s) ≡ s
law1 = {!!}

law2 : {`M : ℕ}{A : Fin (suc `M)}(n : ℕ) → enc `M {A = A} (dec `M n) ≡ n
law2 = {!!}
