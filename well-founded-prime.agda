Rel : Set → Set₁
Rel A = A → A → Set

data Acc {A : Set} (_<_ : Rel A) (x : A) : Set where
  acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x
