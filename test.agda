-- well-founded (induction)
{--
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (trans)
open DecTotalOrder decTotalOrder using (trans)

⌊n/2⌋≤n : ∀ n → ⌊ n /2⌋ ≤ n
⌊n/2⌋≤n n = ≤′⇒≤ (⌊n/2⌋≤′n n)

-------------------------

-- View Type
-- Accessibility(Accessible)
data Acc (n : ℕ) : Set where
  acc : (∀ m → m < n → Acc m) → Acc n

WF : Set
WF = ∀ n → Acc n

-- View Function
<-wf : ∀ n → Acc n -- WF
<-wf n = acc (go n)
  where
    go : ∀ n m → m < n → Acc m
    go zero m ()
    go (suc n) zero m<n = acc (λ _ ())
    go (suc n) (suc m) (s≤s m<n) = acc (λ k k<sm → go n k (trans k<sm m<n))

-------
{--
const0 : ℕ → ℕ
const0 n = const0' n (<-wf n)
  where
    const0' : (n : ℕ) → Acc n → ℕ
    const0' zero a = 0
    const0' (suc n) (acc rs) = const0' ⌊ n /2⌋ (rs ⌊ n /2⌋ (s≤s (⌊n/2⌋≤n n)))

div : (n d : ℕ) → {≢0 : d ≢ 0} → ℕ
div n d {≢0} = div' n d {≢0} (<-wf n)
  where
    div' : (n d : ℕ) → {≢0 : d ≢ 0} → Acc n → ℕ
    div' n zero {≢0} a = ⊥-elim (≢0 refl)
    div' zero (suc d) {≢0} a = 0
    div' (suc n) (suc d) {≢0} (acc rs)
      = suc (div' (suc n ∸ suc d) (suc d) {≢0} (rs (n ∸ d) (s≤s (n∸m≤n d n))))
--}

--                         In = acc
-- Acc n  <------------------------------ ∀ n → (∀ m → m < n → Acc m)
--      |                                                                  |
--      |  cata φn                                                 | ∀ n → (∀ m → m < n → cata φ m)
--      |                                                                  |
--      v                                                                 v
--    P  n  <------------------------------ ∀ n → (∀ m → m < n → P m)
--                        φ n
fold-acc : {P : ℕ → Set} → (∀ n → (∀ m → m < n → P m) → P n) → ∀ n → Acc n → P n
fold-acc {P} φ n (acc rs) = φ n (λ m m<n → fold-acc {P} φ m (rs m m<n))

-- Recursor
rec-wf : {P : ℕ → Set} → WF → (∀ n → (∀ m → m < n → P m) → P n) → ∀ n → P n
rec-wf {P} wf φ n = fold-acc {P} φ n (wf n)

const0 : ℕ → ℕ
const0 = rec-wf <-wf body
  where
    body : ∀ n → (∀ m → m < n → ℕ) → ℕ
    body zero rs = 0
    body (suc n) rs = rs ⌊ n /2⌋ (s≤s (⌊n/2⌋≤n n))

div : (n d : ℕ) → {≢0 : d ≢ 0} → ℕ
div n d {≢0} = rec-wf <-wf (body d ≢0) n
  where
    body : ∀ d → (d ≢ 0) → ∀ n → (∀ m → m < n → ℕ) → ℕ
    body zero ≢0 n rs = ⊥-elim (≢0 refl)
    body (suc d) ≢0 zero rs = 0
    body (suc d) ≢0 (suc n) rs = suc (rs (suc n ∸ suc d) (s≤s (n∸m≤n d n)))
--}

-- open import Induction.WellFounded
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Induction.Nat
open import Relation.Binary.PropositionalEquality

const0 : ℕ → ℕ
const0 = <-rec _ body
  where
    body : ∀ x → (∀ y → y <′ x → ℕ) → ℕ
    body zero rs = 0
    body (suc n) rs = rs ⌊ n /2⌋ (s≤′s (⌊n/2⌋≤′n n))

div : (n d : ℕ) → {≢0 : d ≢ 0} → ℕ
div n d {≢0} = <-rec _ (body d ≢0) n
  where
    body : ∀ d → (d ≢ 0) → ∀ n → (∀ m → m <′ n → ℕ) → ℕ
    body zero ≢0 n₁ rs = ⊥-elim (≢0 refl)
    body (suc d) ≢0 zero rs = 0
    body (suc d) ≢1 (suc n) rs = suc (rs (suc n ∸ suc d) (s≤′s (≤⇒≤′ (n∸m≤n d n))))
