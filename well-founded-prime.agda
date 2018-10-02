-- | generalized to well-founded and recursive builder and recursor
Rel : Set → Set₁
Rel A = A → A → Set

data Acc {A : Set} (_<_ : Rel A) (x : A) : Set where
  acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

WellFound : ∀ {A} → Rel A → Set
WellFound _<_ = ∀ x → Acc _<_ x

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary hiding (Rel)
open DecTotalOrder ≤-decTotalOrder using (trans)

<-wf : WellFound _<_
<-wf n = acc (go n)
  where
    go : ∀ n m → m < n → Acc (λ k → _≤_ (suc k)) m
    go zero m ()
    go (suc n) zero m<n = acc (λ _ ())
    go (suc n) (suc m) (s≤s m<n) = acc (λ k k<sm → go n k (trans k<sm m<n))


-- |                     In = acc
--   Acc _<_ z   <------------------------- ∀ z → (∀ y → y < z → Acc _<_ y)
--       |                                             |
--       |⦇φ⦈ z                                        | ∀ z → (∀ y → y < z → ⦇φ⦈ y)
--       |                                             |
--       v                                             v
--      P z      <------------------------- ∀ z → (∀ y → y < z → P y)
--                         φ
fold-acc : ∀ {A} (_<_ : Rel A) {P : A → Set} → (∀ x → (∀ y → y < x → P y) → P x) → ∀ z → Acc _<_ z → P z
fold-acc _<_ φ z (acc rec) = φ z (λ y y<z → fold-acc _<_ φ y (rec y y<z))
