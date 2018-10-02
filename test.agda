--  Well-founded
open import Data.Nat
open import Relation.Binary
open DecTotalOrder decTotalOrder using (trans)

-- | view type
data Acc (n : ℕ) : Set where
  acc : (∀ m → m < n → Acc m) → Acc n

-- view function
<-wf : ∀ n → Acc n
<-wf n = acc (go n)
  where
    go : ∀ n m → m < n → Acc m
    go zero m ()
    go (suc n) zero p = acc (λ _ ())
    go (suc n) (suc m) (s≤s m<n) = acc (λ k k<sm → go n k (trans k<sm m<n))

{-# TERMINATING #-}
f : ℕ → ℕ
f zero = 0
f (suc n) = f ⌊ n /2⌋

g : ℕ → ℕ
g n =  go n (<-wf n) 
  where
    go : ∀ n → Acc n → ℕ
    go zero a = 0
    go (suc n) (acc a) = go ⌊ n /2⌋ (a ⌊ n /2⌋ (s≤s (/2-less n)))
      where
        /2-less : ∀ n → ⌊ n /2⌋ ≤ n
        /2-less zero = z≤n
        /2-less (suc zero) = z≤n
        /2-less (suc (suc n)) = s≤s (trans (/2-less n) (n≤sn n))
          where
            n≤sn : ∀ n → n ≤ suc n
            n≤sn zero = z≤n
            n≤sn (suc n) = s≤s (n≤sn n)

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty

{-# TERMINATING #-}
div : ℕ → (d : ℕ) → {≢0 : d ≢ 0} → ℕ
div zero d {≢0} = 0
div (suc n) zero {≢0} = ⊥-elim (≢0 refl)
div (suc n) (suc d) {≢0} = suc (div (suc n ∸ suc d) (suc d) {≢0})

open import Data.Nat.Properties

div-wf : (n : ℕ) → (d : ℕ) → {≢0 : d ≢ 0} → Acc n → ℕ
div-wf n zero {≢0} a = ⊥-elim (≢0 refl)
div-wf zero (suc d) {≢0} a = 0
div-wf (suc n) (suc d) {≢0} (acc a) = suc (div-wf (suc n ∸ suc d) (suc d) {≢0} (a (n ∸ d) (s≤s ( n∸d≤n n d ≢0 ))))
  where
    n∸d≤n : ∀ n d → (≢0 : suc d ≢ 0) → n ∸ d ≤ n
    n∸d≤n n d ≢0 = ≤′⇒≤ (n∸d≤′n n d ≢0)
      where
        n∸d≤′n : ∀ n d → (≢0 : suc d ≢ 0) → n ∸ d ≤′ n
        n∸d≤′n n zero ≢0 = ≤′-refl
        n∸d≤′n zero (suc d) ≢0 = ≤′-refl
        n∸d≤′n (suc n) (suc d) ≢0 = ≤′-step (n∸d≤′n n d (λ ()))
