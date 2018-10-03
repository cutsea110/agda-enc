open import Data.Fin hiding (_+_; _<_; _≤_) renaming (zero to fzero; suc to fsuc; pred to fpred)
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary
open DecTotalOrder ≤-decTotalOrder using (trans)
open import Data.Nat.DivMod

data List (`M : ℕ) (A : Fin (suc `M)) : Set where
  ⟨⟩ : List `M A
  ⟨_⟩⌢_ : Fin (suc `M) → List `M A → List `M A

{--
data Enc (`M : ℕ){A : Fin (suc `M)} : List `M A → Set where
  nil  : Enc `M ⟨⟩
  cons : (x : Fin (suc `M)) → (s : List `M A) → Enc `M (⟨ x ⟩⌢ s)
--}

data Acc (n : ℕ) : Set where
  acc : (∀ m → m < n → Acc m) → Acc n

WF : Set
WF = ∀ n → Acc n

<-wf : ∀ n → Acc n
<-wf n = acc (go n)
  where
    go : ∀ n m → m < n → Acc m
    go zero m ()
    go (suc n) zero p = acc (λ _ ())
    go (suc n) (suc m) (s≤s m<n) = acc (λ k k<sm → go n k (trans k<sm m<n))

-- | {M=n} [a_0,a_1,a_2,...] ==> (1+a_0) + n(1+a_1) + n^2(1+a_2) + .. + n^i(1+a_i) + ...
enc : (`M : ℕ) {A : Fin (suc `M)} → List `M A → ℕ
enc `M ⟨⟩ = 0
enc `M (⟨ x ⟩⌢ s) = 1 + toℕ x + suc `M * enc `M s

{-# TERMINATING #-}
dec : (`M : ℕ) {A : Fin (suc `M)} → ℕ → List `M A
dec `M zero = ⟨⟩
dec `M (suc n) with n div (suc `M) | n mod (suc `M)
... | q | r = ⟨ r ⟩⌢ dec `M q

open import Agda.Builtin.Nat using (div-helper)
open import Relation.Binary.PropositionalEquality

lemma : ∀ `M n → div-helper 0 `M n `M ≤ n
lemma `M zero = z≤n
lemma zero (suc n) = {!!}
lemma (suc `M) (suc n) = {!!}


dec' : (`M : ℕ) {A : Fin (suc `M)} → ℕ → List `M A
dec' `M n = go `M n (<-wf n)
  where
    go : ∀ `M n → Acc n → {A : Fin (suc `M)} → List `M A
    go `M zero a = ⟨⟩
    go `M (suc n) (acc a) = ⟨ n mod (suc `M) ⟩⌢ go `M (n div (suc `M)) (a (div-helper zero `M n `M) (s≤s ( lemma `M n)))
    
law1 : {`M : ℕ}{A : Fin (suc `M)}{s : List `M A} → dec `M (enc `M s) ≡ s
law1 = {!!}

law2 : {`M : ℕ}{A : Fin (suc `M)}(n : ℕ) → enc `M {A = A} (dec `M n) ≡ n
law2 = {!!}
