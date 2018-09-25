open import Data.Nat
open import Induction.WellFounded
open import Induction.Nat

s≤′s : ∀ {n m} → n ≤′ m → suc n ≤′ suc m
s≤′s ≤′-refl = ≤′-refl
s≤′s (≤′-step prf) = ≤′-step (s≤′s prf)

proof : ∀ n → ⌊ n /2⌋ ≤′ n
proof zero = ≤′-refl
proof (suc zero) = ≤′-step (proof zero)
proof (suc (suc n)) = ≤′-step (s≤′s (proof n))

f : ℕ → ℕ
f = <-rec (λ _ → ℕ) helper
  where
    helper : (n : ℕ) → (∀ m → m <′ n → ℕ) → ℕ
    helper zero rec = 0
    helper (suc n) rec = rec ⌊ n /2⌋ (s≤′s (proof n))
