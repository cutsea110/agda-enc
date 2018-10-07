open import Function
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary
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
    go (suc n) zero (s≤s p) = acc (λ _ ())
    go (suc n) (suc m) (s≤s m<n) = acc (λ k k<sm → go n k (trans k<sm m<n))

open import Relation.Binary.PropositionalEquality hiding (trans)
open import Relation.Nullary
open import Data.Empty

⌊n/2⌋≤n : ∀ n → ⌊ n /2⌋ ≤ n
⌊n/2⌋≤n zero = z≤n
⌊n/2⌋≤n (suc zero) = z≤n
⌊n/2⌋≤n (suc (suc n)) = s≤s (trans (⌊n/2⌋≤n n) (n≤sn n))
  where
    n≤sn : ∀ n → n ≤ suc n
    n≤sn zero = z≤n
    n≤sn (suc n) = s≤s (n≤sn n)

test0 : ℕ → ℕ
test0 n = test1 n (<-wf n)
  where
    test1 : (n : ℕ) → Acc n → ℕ
    test1 zero a = 0
    test1 (suc n) (acc a) = test1 ⌊ n /2⌋ (a ⌊ n /2⌋ (s≤s (⌊n/2⌋≤n n)))


div : (n : ℕ) → (d : ℕ) → {≢0 : d ≢ 0} → ℕ
div n d {≢0} = div' n d {≢0} (<-wf n)
  where
    div' : (n : ℕ) → (d : ℕ) → {≢0 : d ≢ 0} → Acc n → ℕ
    div' n zero {≢0} a = ⊥-elim (≢0 refl)
    div' zero (suc d) {≢0} a = 0
    div' (suc n) (suc d) {≢0} (acc r) = div' (suc n ∸ suc d) (suc d) {≢0} (r (n ∸ d) (s≤s (≤′⇒≤ (n∸d<sn n d))))
      where
        n∸d<sn : ∀ n d → n ∸ d ≤′ n
        n∸d<sn n zero = ≤′-refl
        n∸d<sn zero (suc d) = ≤′-refl
        n∸d<sn (suc n) (suc d) = ≤′-step (n∸d<sn n d)

fold-acc : {P : ℕ → Set} → (∀ n → (∀ m → m < n → P m) → P n) → ∀ x → Acc x → P x
fold-acc {P} φ x (acc r) = φ x (λ y y<x → fold-acc {P} φ y (r y y<x))

rec-wf : {P : ℕ → Set} → WF → (∀ n → (∀ m → m < n → P m) → P n) → ∀ x → P x
rec-wf {P} wf φ x = fold-acc {P} φ x (wf x)

test0' : ℕ → ℕ
test0' n = rec-wf <-wf body n
  where
    body : ∀ n → (∀ m → suc m ≤ n → ℕ) → ℕ
    body zero r = 0
    body (suc n) r = r n (s≤s (≤′⇒≤ ≤′-refl))

div' : (n : ℕ) → (d : ℕ) → {≢0 : d ≢ 0} → ℕ
div' n d {≢0} = rec-wf <-wf ( body d ≢0 ) n
  where
    body : ∀ d → (≢0 :  d ≢ 0) → ∀ n → (∀ m → m < n → ℕ) → ℕ
    body zero ≢0 n r = ⊥-elim (≢0 refl)
    body (suc d) ≢1 zero r = 0
    body (suc d) ≢1 (suc n) r = suc (r (suc n ∸ suc d) (s≤s (≤′⇒≤ (n∸d≤′n n d))))
      where
        n∸d≤′n : ∀ n d → n ∸ d ≤′ n
        n∸d≤′n n zero = ≤′-refl
        n∸d≤′n zero (suc d) = ≤′-refl
        n∸d≤′n (suc n) (suc d) = ≤′-step (n∸d≤′n n d)

open import Induction.WellFounded
open import Induction.Nat


open import Relation.Unary
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
  
twice : ℕ → ℕ
twice = rec _ (λ
  { zero y → zero
  ; (suc n) twice-n → suc (suc twice-n)
  })

mutual

  half₁-step : ∀ x → CRec lzero (λ _ → ℕ) x → ℕ
  half₁-step = λ
    { zero rs → 0
    ; (suc zero) rs → 0
    ; (suc (suc n)) (pred₁n , half₁n , rs) → suc half₁n
    }

  half₁ : ℕ → ℕ
  half₁ = cRec _ half₁-step

  half₂-step : ∀ x → (∀ y → suc y ≤′ x → ℕ) → ℕ
  half₂-step = λ
    { zero rs → 0
    ; (suc zero) rs → 0
    ; (suc (suc n)) rs → suc (rs n (≤′-step ≤′-refl))
    }
  half₂ : ℕ → ℕ
  half₂ = <-rec (λ x → ℕ) half₂-step

  half₁-2+ : ∀ n → half₁ (2 + n) ≡ 1 + half₁ n
  half₁-2+ n = begin

    half₁ (2 + n)  ≡⟨⟩
  
    cRec (λ x → ℕ) half₁-step (2 + n) ≡⟨⟩

    half₁-step (2 + n) (cRec-builder (λ x → ℕ) half₁-step (2 + n)) ≡⟨⟩

    half₁-step (2 + n)
      (let ih = cRec-builder (λ x → ℕ) half₁-step (1 + n)
        in half₁-step (1 + n) ih , ih) ≡⟨⟩

    half₁-step (2 + n)
      (let ih = cRec-builder (λ x → ℕ) half₁-step n
        in half₁-step (1 + n) (half₁-step n ih , ih) , half₁-step n ih , ih) ≡⟨⟩

    1 + half₁-step n (cRec-builder (λ x → ℕ) half₁-step n) ≡⟨⟩

    1 + cRec (λ x → ℕ) half₁-step n ≡⟨⟩

    1 + half₁ n  ∎
    where open ≡-Reasoning
    
  half₂-2+ : ∀ n → half₂ (2 + n) ≡ 1 + half₂ n
  half₂-2+ n = begin
  
    half₂ (2 + n) ≡⟨⟩

    <-rec (λ x → ℕ) half₂-step (2 + n) ≡⟨⟩

    half₂-step (2 + n) (<-rec-builder (λ x → ℕ) half₂-step (2 + n)) ≡⟨⟩

    1 + <-rec-builder (λ x → ℕ) half₂-step (2 + n) n (≤′-step ≤′-refl) ≡⟨⟩

    1 + Some.wfRec-builder (λ x → ℕ) half₂-step (2 + n)
        (<-well-founded (2 + n)) n (≤′-step ≤′-refl) ≡⟨⟩

    1 + Some.wfRec-builder (λ x → ℕ) half₂-step (2 + n)
        (acc (<-well-founded′ (2 + n))) n (≤′-step ≤′-refl) ≡⟨⟩

    1 + half₂-step n
        (Some.wfRec-builder (λ x → ℕ) half₂-step n
          (<-well-founded′ (2 + n) n (≤′-step ≤′-refl))) ≡⟨⟩

    1 + half₂-step n
        (Some.wfRec-builder (λ x → ℕ) half₂-step n
          (<-well-founded′ (1 + n) n ≤′-refl)) ≡⟨⟩

    1 + half₂-step n
        (Some.wfRec-builder (λ x → ℕ) half₂-step n (<-well-founded n)) ≡⟨⟩

    1 + half₂-step n (<-rec-builder (λ x → ℕ) half₂-step n) ≡⟨⟩

    1 + <-rec (λ x → ℕ) half₂-step n ≡⟨⟩
    
    1 + half₂ n ∎
    
    where open ≡-Reasoning

  half₁-+₁ : ∀ n → half₁ (twice n) ≡ n
  half₁-+₁ = cRec _ λ
    { zero x → refl
    ; (suc zero) x → refl
    ; (suc (suc n)) (_ , half₁twice-n≡n , _) → cong (suc ∘ suc) half₁twice-n≡n
    }

  half₂-+₁ : ∀ n → half₂ (twice n) ≡ n
  half₂-+₁ = cRec _ λ
    { zero x → refl
    ; (suc zero) x → refl
    ; (suc (suc n)) (_ , half₁twice-n≡n , _) → cong (suc ∘ suc) half₁twice-n≡n
    }

  half₁-+₂ : ∀ n → half₁ (twice n) ≡ n
  half₁-+₂ = <-rec _ λ
    { zero x → refl
    ; (suc zero) x → refl
    ; (suc (suc n)) rec → cong (suc ∘ suc) (rec n (≤′-step ≤′-refl))
    }
