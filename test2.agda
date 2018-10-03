open import Data.Nat
open import Relation.Binary
open DecTotalOrder decTotalOrder using (trans)

-- | View Type
-- Accessibility(Accessible) : reach to every y from x
data Acc (x : ℕ) : Set where
  acc : (∀ y → y < x → Acc y) → Acc x

-- well-fouded over _<_
-- WF : Set
-- WF = ∀ n → Acc n

-- | View function
-- _<_ is well-founded relation
<-wf : ∀ n → Acc n
<-wf n = acc (go n)
  where
    go : ∀ n m → m < n → Acc m
    go zero m ()
    go (suc n) zero m<n = acc (λ _ ())
    go (suc n) (suc m) (s≤s m<n) = acc (λ y y<sm → go n y (trans y<sm m<n))

/2-less : ∀ n → ⌊ n /2⌋ ≤ n
/2-less zero = z≤n
/2-less (suc zero) = z≤n
/2-less (suc (suc n)) = s≤s (trans (/2-less n) (n≤sn n))
  where
    n≤sn : ∀ n → n ≤ suc n
    n≤sn zero = z≤n
    n≤sn (suc n) = s≤s (n≤sn n)

test0 : ℕ → ℕ
test0 n = test0' n (<-wf n)
  where
    test0' : (n : ℕ) →  Acc n → ℕ
    test0' zero a = 0
    test0' (suc n) (acc a) = test0' ⌊ n /2⌋ (a ⌊ n /2⌋ (s≤s (/2-less n)))

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Data.Nat.Properties

div : (n : ℕ) → (d : ℕ) → {≢0 : d ≢ 0} → ℕ
div n d {≢0} = div' n d {≢0} (<-wf n)
  where
    div' : (n : ℕ) → (d : ℕ)  → {≢0 : d ≢ 0} → Acc n → ℕ
    div' n zero {≢0} a = ⊥-elim (≢0 refl)
    div' zero (suc d) {≢0} a = 0
    div' (suc n) (suc d) {≢0} (acc a) = suc (div' (suc n ∸ suc d) (suc d) {≢0} (a (n ∸ d) (s≤s ( n∸d≤n n d ))))
      where
        n∸d≤n : ∀ n d → n ∸ d ≤ n
        n∸d≤n n d = ≤′⇒≤ (n∸d≤′n n d )
          where
            n∸d≤′n : ∀ n d → n ∸ d ≤′ n
            n∸d≤′n n zero = ≤′-refl
            n∸d≤′n zero (suc d) = ≤′-refl
            n∸d≤′n (suc n₂) (suc d₂) = ≤′-step (n∸d≤′n n₂ d₂)
