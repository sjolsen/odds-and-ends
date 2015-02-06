module BNatFib where
  open import BNat
  open import Data.Nat using (zero; suc; _⊔_)
  open import Data.Product
  open import Data.Colist renaming (map to comap)
  open import Data.String using (String)
  open import Function
  open import Coinduction
  open import IO

  data ℕ₂′ : Set where
    lift : ∀ {i} → ℕ₂ {i} → ℕ₂′

  zero-extend : ∀ {i j} →  ℕ₂ {i} → ℕ₂ {j} → ℕ₂ {i ⊔ j} × ℕ₂ {i ⊔ j}
  zero-extend {zero}  {zero}           m           n  = (m , n)
  zero-extend {zero}  {suc j} (bit     m)          n  = ((bits 0₂ m) , n)
  zero-extend {suc i} {zero}           m  (bit     n) = (m , bits 0₂ n)
  zero-extend {suc i} {suc j} (bits ms m) (bits ns n) with zero-extend ms ns
  ... | (ms′ , ns′) = ((bits ms′ m) , (bits ns′ n))

  plus : ℕ₂′ → ℕ₂′ → ℕ₂′
  plus (lift m) (lift n) = lift (uncurry′ _+₂_ $ zero-extend m n)

  fibstep : ℕ₂′ × ℕ₂′ → ℕ₂′ × ℕ₂′
  fibstep (m , n) = (n , plus m n)

  iterate : ∀ {ℓ} {A : Set ℓ} → (A → A) → A → Colist A
  iterate f x = x ∷ ♯ iterate f (f x)

  main = run (mapM putStrLn (comap (show′ ∘ proj₁) (iterate fibstep (lift {0} 1₂ , lift {0} 1₂))))
    where show′ : ℕ₂′ → String
          show′ (lift n) = show n
