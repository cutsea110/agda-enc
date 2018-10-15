open import Data.Fin hiding (_+_; _<_; _≤_) renaming (zero to fzero; suc to fsuc; pred to fpred)
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary
open DecTotalOrder decTotalOrder using (trans)
open import Data.Nat.DivMod
open import Induction.Nat

data List (`M : ℕ) (A : Fin (suc `M)) : Set where
  ⟨⟩ : List `M A
  ⟨_⟩⌢_ :  Fin (suc `M) → List `M A → List `M A

-- | {M=n} [a_0,a_1,a_2,...] ==> (1+a_0) + n(1+a_1) + n^2(1+a_2) + .. + n^i(1+a_i) + ...
enc : (`M : ℕ) {A : Fin (suc `M)} → List `M A → ℕ
enc `M ⟨⟩ = 0
enc `M (⟨ x ⟩⌢ s) = 1 + toℕ x + suc `M * enc `M s
{--
dec : (`M : ℕ) {A : Fin (suc `M)} → ℕ → List `M A
dec `M zero = ⟨⟩
dec `M (suc n) with n div (suc `M) | n mod (suc `M)
... | q | r = ⟨ r ⟩⌢ dec `M q
--}

open import Agda.Builtin.Nat

lemma : ∀ `M n → div-helper 0 `M n `M ≤′ n
lemma `M n = {!!}

dec : (`M : ℕ) {A : Fin (suc `M)} → ℕ → List `M A
dec `M n = <-rec _ (body `M) n
  where
    body : ∀ `M {A : Fin (suc `M)} → ∀ n → (∀ m →  m <′ n → List `M A) → List `M A
    body `M zero rs = ⟨⟩
    body `M (suc n) rs = ⟨ n mod (suc `M) ⟩⌢ (rs (n div (suc `M)) (s≤′s (lemma `M n)))


open import Relation.Binary.PropositionalEquality

law1 : {`M : ℕ}{A : Fin (suc `M)}{s : List `M A} → dec `M (enc `M s) ≡ s
law1 = {!!}

law2 : {`M : ℕ}{A : Fin (suc `M)}(n : ℕ) → enc `M {A = A} (dec `M n) ≡ n
law2 = {!!}
