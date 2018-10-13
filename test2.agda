{--
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (trans)
open import Data.Empty
open import Relation.Nullary

open DecTotalOrder decTotalOrder using (trans)


-- | View Type
data Acc (n : ℕ) : Set where
  acc : (∀ m → m < n → Acc m) → Acc n

WF : Set
WF = ∀ n → Acc n

-- | View Function
<-wf : ∀ n → Acc n
<-wf n = acc (go n)
  where
    go : ∀ n m → m < n → Acc m
    go zero m ()
    go (suc n) zero p = acc (λ _ ())
    go (suc n) (suc m) (s≤s m<n) = acc (λ k k<sm → go n k (trans k<sm m<n))

⌊n/2⌋≤n : ∀ n → ⌊ n /2⌋ ≤ n
⌊n/2⌋≤n zero = z≤n
⌊n/2⌋≤n (suc zero) = z≤n
⌊n/2⌋≤n (suc (suc n)) = s≤s (trans (⌊n/2⌋≤n n) (n≤sn n))
  where
    n≤sn : ∀ n → n ≤ suc n
    n≤sn zero = z≤n
    n≤sn (suc n) = s≤s (n≤sn n)


const0 : ℕ → ℕ
const0 n = const0-wf n (<-wf n)
  where
    const0-wf : (n : ℕ) → Acc n → ℕ
    const0-wf zero a = 0
    const0-wf (suc n) (acc rec) = const0-wf ⌊ n /2⌋ (rec ⌊ n /2⌋ (s≤s (⌊n/2⌋≤n n)))

n∸d≤′n : ∀ n d → n ∸ d ≤′ n
n∸d≤′n n zero = ≤′-refl
n∸d≤′n zero (suc d) = ≤′-refl
n∸d≤′n (suc n) (suc d) = ≤′-step (n∸d≤′n n d)

div : (n d : ℕ) → {≢0 : d ≢ 0} → ℕ
div n d {≢0} = div-wf n d {≢0} (<-wf n)
  where
    div-wf : (n d : ℕ) → {≢0 : d ≢ 0} → Acc n → ℕ
    div-wf n zero {≢0} a = ⊥-elim (≢0 refl)
    div-wf zero (suc d) {≢0} a = 0
    div-wf (suc n) (suc d) {≢0} (acc rec) = div-wf (suc n ∸ suc d) (suc d) {≢0} (rec (n ∸ d) (s≤s (≤′⇒≤ (n∸d≤′n n d))))

--                                     In = acc
-- Acc n <----------------------------------- (λn  → (λ m → m < n → Acc m) → P n)
--      |                                                                     |
--      |                                                                     |
--      | cata = u ψ n                                            | (λ n → (λ m → m < n → cata m) → cata n)
--      |                                                                     |
--      v                                                                    v
--    P n  <----------------------------------- (λ n → (λ m → m < n → P m) → P n)
--                                  ψn
fold-acc :  {P : ℕ → Set} → (∀ n → (∀ m → m < n → P m) → P n) → ∀ n → Acc n → P n
fold-acc {P} ψ n  (acc rec) = ψ n (λ m m<n → fold-acc {P} ψ m (rec m m<n))

rec-wf  : {P : ℕ → Set} → WF → (∀ n → (∀ m → m < n → P m) → P n) → ∀ n → P n
rec-wf {P} wf ψ n = fold-acc {P} ψ n (wf n)

const0' : ℕ → ℕ
const0' n = rec-wf <-wf body n
  where
    body : ∀ n → (∀ m → m < n → ℕ) → ℕ
    body zero rec = 0
    body (suc n) rec = rec ⌊ n /2⌋ (s≤s (⌊n/2⌋≤n n))

div' : (n  d : ℕ) → {≢0 : d ≢ 0} → ℕ
div' n d {≢0} = rec-wf <-wf (body d ≢0) n
  where
    body : ∀ d → (d ≢ 0) → ∀ n → (∀ m → suc m ≤ n → ℕ) → ℕ
    body zero ≢0 n rec = ⊥-elim (≢0 refl)
    body (suc d) ≢0 zero rec = 0
    body (suc d) ≢0 (suc n) rec = suc (rec (suc n ∸ suc d) (s≤s (≤′⇒≤ (n∸d≤′n n d))))
--}

open import Data.Nat
open import Data.Nat.Properties
open import Induction.WellFounded
open import Induction.Nat using (<-well-founded)

open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary
open DecTotalOrder decTotalOrder using (trans)

open All <-well-founded lzero renaming (wfRec to <-rec)

open import Data.Nat

const0 : ℕ → ℕ
const0 = <-rec _ λ
  { zero p → 0
  ; (suc n) p → p ⌊ n /2⌋ (≤⇒≤′ (s≤s (≤′⇒≤ (⌊n/2⌋≤′n n))))
  }
{--
const0 : ℕ → ℕ
const0 n = <-rec _ body n
  where
    body : ∀ n → (∀ m → m <′ n → ℕ) → ℕ
    body zero p = 0
    body (suc n) p = p ⌊ n /2⌋ (≤⇒≤′ (s≤s (≤′⇒≤ (⌊n/2⌋≤′n n))))
--}

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary

div : (n d : ℕ) → {≢0 : d ≢ 0} → ℕ
div n d {≢0} = <-rec _ (body d ≢0) n
  where
    body : ∀ d → (d ≢ 0) → ∀ n → (∀ m →  m <′ n → ℕ) → ℕ
    body zero ≢0 n rec = ⊥-elim (≢0 refl)
    body (suc d) ≢0 zero rec = 0
    body (suc d) ≢0 (suc n) rec = suc (rec (suc n ∸ suc d) (≤⇒≤′ (s≤s (n∸m≤n d n))))
