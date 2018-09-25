open import Data.Nat
open import Relation.Binary
open DecTotalOrder decTotalOrder using (trans)

data Acc (n : ℕ) : Set where
  acc : (∀ m → m < n → Acc m) → Acc n

triv0 : Acc 0
triv0 = acc help
  where
    help : ∀ m → suc m ≤ 0 → Acc m
    help m ()

triv1 : Acc 1
triv1 = acc help
  where
    help : ∀ m → suc m ≤ 1 → Acc m
    help .0 (s≤s z≤n) = triv0

triv2 : Acc 2
triv2 = acc help
  where
    help : ∀ m → suc m ≤ 2 → Acc m
    help .0 (s≤s z≤n) = triv0
    help .1 (s≤s (s≤s z≤n)) = triv1

triv3 : Acc 3
triv3 = acc help
  where
    help : ∀ m → suc m ≤ 3 → Acc m
    help .0 (s≤s z≤n) = triv0
    help .1 (s≤s (s≤s z≤n)) = triv1
    help .2 (s≤s (s≤s (s≤s z≤n))) = triv2

WF : Set
WF = ∀ n → Acc n

<-wf : WF
<-wf n = acc (go n)
  where
    -- NOTICE! : go is nicely structurally recursive.
    go : ∀ n m → m < n → Acc m
    go zero m ()
    go (suc n) zero (s≤s z≤n) = acc (λ _ ())
    go (suc n) (suc m) (s≤s m<n) = acc (λ o o<sm → go n o (trans o<sm m<n))

-- prove
/2-less : ∀ n → ⌊ n /2⌋ ≤ n
/2-less zero = z≤n
/2-less (suc zero) = z≤n
/2-less (suc (suc n)) = s≤s (trans (/2-less n) (right n))
  where
    right : ∀ n → n ≤ suc n
    right zero = z≤n
    right (suc n) = s≤s (right n)

f : ℕ → ℕ
f n = go n (<-wf n)
  where
    go : ∀ n → Acc n → ℕ
    go zero _ = 0
    -- NOTICE! structurally recursive thanks to Acc :
    --   the recursive calls happen on arguments with one acc constructor peeled off.
    go (suc n) (acc a) = go ⌊ n /2⌋ (a ⌊ n /2⌋ (s≤s (/2-less n)))
