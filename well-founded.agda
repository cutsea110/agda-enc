open import Data.Nat

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
