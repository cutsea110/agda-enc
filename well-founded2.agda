open import Data.Nat
open import Data.Nat.Properties -- using (s≤′s)
open import Induction.WellFounded
open import Induction.Nat
open import Relation.Binary
open DecTotalOrder ≤-decTotalOrder using (trans)

proof : ∀ n → ⌊ n /2⌋ ≤ n
proof zero = z≤n
proof (suc zero) = z≤n
proof (suc (suc n)) = s≤s (trans (proof n) (help n))
  where
    help : ∀ n → n ≤ suc n
    help zero = z≤n
    help (suc n) = s≤s (help n)

f : ℕ → ℕ
f = <-rec (λ _ → ℕ) helper
  where
    helper : ∀ n → (∀ m → m < n → ℕ) → ℕ
    helper zero rec = 0
    helper (suc n) rec = rec ⌊ n /2⌋ (s≤s (proof n))
