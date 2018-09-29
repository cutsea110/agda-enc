open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary
open DecTotalOrder ≤-decTotalOrder using (trans)

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

triv⌊1/2⌋ : Acc ⌊ 1 /2⌋
triv⌊1/2⌋ = acc λ m ()

triv⌊2/2⌋ : Acc ⌊ 2 /2⌋
triv⌊2/2⌋ = acc help
  where
    help : ∀ m → suc m ≤ 1 → Acc m
    help zero (s≤s z≤n) = triv⌊1/2⌋
    help (suc m) (s≤s ())

triv⌊3/2⌋ : Acc ⌊ 3 /2⌋
triv⌊3/2⌋ = acc help
  where
    help : ∀ m → suc m ≤ 1 → Acc m
    help zero (s≤s z≤n) = triv⌊1/2⌋
    help (suc m) (s≤s ())

triv⌊4/2⌋ : Acc ⌊ 4 /2⌋
triv⌊4/2⌋ = acc help
  where
    help : ∀ m → suc m ≤ 2 → Acc m
    help zero (s≤s z≤n) = triv⌊1/2⌋
    help (suc .0) (s≤s (s≤s z≤n)) = triv⌊2/2⌋
    
triv⌊5/2⌋ : Acc ⌊ 5 /2⌋
triv⌊5/2⌋ = acc help
  where
    help : ∀ m → suc m ≤ 2 → Acc m
    help zero (s≤s z≤n) = triv⌊1/2⌋
    help (suc .0) (s≤s (s≤s z≤n)) = triv⌊2/2⌋

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd  : (k : ℕ) → Parity (k * 2 + 1)

parity : (n : ℕ) → Parity n
parity zero = even zero
parity (suc zero) = odd zero
parity (suc (suc n)) with parity n
parity (suc (suc .(k * 2))) | even k = even (suc k)
parity (suc (suc .(k * 2 + 1))) | odd k = odd (suc k)

open import Relation.Binary.PropositionalEquality hiding (trans)

⌊k*2/2⌋≡k : ∀ k → ⌊ k * 2 /2⌋ ≡ k
⌊k*2/2⌋≡k zero = refl
⌊k*2/2⌋≡k (suc k) = cong suc (⌊k*2/2⌋≡k k)

⌊k*2+1/2⌋≡k : ∀ k → ⌊ k * 2 + 1 /2⌋ ≡ k
⌊k*2+1/2⌋≡k zero = refl
⌊k*2+1/2⌋≡k (suc k) = cong suc (⌊k*2+1/2⌋≡k k)

-- NOTICE! : go is nicely structurally recursive.
go : ∀ k m → suc m ≤ k → Acc m
go zero m ()
go (suc k) zero p = acc λ _ ()
go (suc k) (suc m) (s≤s m<k) = acc λ m₁ m₁<sm → go k m₁ (trans m₁<sm m<k)

triv⌊n/2⌋ : ∀ n → Acc ⌊ n /2⌋
triv⌊n/2⌋ n with parity n
triv⌊n/2⌋ .(k * 2) | even k rewrite ⌊k*2/2⌋≡k k = acc (go k)
triv⌊n/2⌋ .(k * 2 + 1) | odd k rewrite ⌊k*2+1/2⌋≡k k = acc (go k)
    
WF : Set
WF = (n : ℕ) → Acc n

<-wf : WF
<-wf n = acc (go n)
    
-- prove
/2-less : ∀ n → ⌊ n /2⌋ ≤ n
/2-less zero = z≤n
/2-less (suc zero) = z≤n
/2-less (suc (suc n)) = s≤s (help n)
  where
    help : ∀ n → ⌊ n /2⌋ ≤ suc n
    help n with /2-less n
    ... | q = trans q (n≤sn n)
      where
        n≤sn : ∀ n → n ≤ suc n
        n≤sn zero = z≤n
        n≤sn (suc n) = s≤s (n≤sn n)
    
f : ℕ → ℕ
f n = go' n (<-wf n)
  where
    go' : ∀ n → Acc n → ℕ
    go' zero _ = 0
    -- NOTICE! structurally recursive thanks to Acc :
    --   the recursive calls happen on arguments with one acc constructor peeled off.
    go' (suc n) (acc a) = go' ⌊ n /2⌋ (a ⌊ n /2⌋ (s≤s (/2-less n)))
