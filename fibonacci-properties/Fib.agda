module Fib where
  open import Data.Empty
  open import Data.Nat
  open import Data.Nat.Properties
  open import Data.Nat.Properties.Simple
  open import Relation.Unary
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning

  f : ℕ → ℕ
  f 0 = 0
  f 1 = 1
  f (suc (suc n)) = f (suc n) + f n


  private
    +-cong = cong₂ _+_
    *-cong = cong₂ _*_

    *-identityˡ : ∀ n → n ≡ 1 * n
    *-identityˡ zero      = refl
    *-identityˡ (suc n-1) = cong suc (*-identityˡ n-1)

    xrefl : ∀ {ℓ} {X : Set ℓ} → (x : X) → x ≡ x
    xrefl x = refl

    +-double : ∀ n → n + n ≡ 2 * n
    +-double zero = refl
    +-double n = begin
      n +     n ≡⟨ +-cong (xrefl n) (*-identityˡ n) ⟩
      n + 1 * n ≡⟨⟩
      2 * n     ∎

    axbycxdy : ∀ a b c d x y → (a * x + b * y) + (c * x + d * y) ≡ (a + c) * x + (b + d) * y
    axbycxdy a b c d x y = begin
      (a * x + b * y) + (c * x + d * y) ≡⟨ sym (+-assoc (a * x + b * y) (c * x) (d * y)) ⟩
      a * x + b * y + c * x + d * y     ≡⟨ +-cong (+-assoc (a * x) (b * y) (c * x)) refl ⟩
      a * x + (b * y + c * x) + d * y   ≡⟨ +-cong (+-cong (xrefl (a * x)) (+-comm (b * y) (c * x))) refl ⟩
      a * x + (c * x + b * y) + d * y   ≡⟨ +-cong (sym (+-assoc (a * x) (c * x) (b * y))) refl ⟩
      a * x + c * x + b * y + d * y     ≡⟨ +-assoc (a * x + c * x) (b * y) (d * y) ⟩
      (a * x + c * x) + (b * y + d * y) ≡⟨ +-cong (sym (distribʳ-*-+ x a c)) (sym (distribʳ-*-+ y b d)) ⟩
      (a + c) * x + (b + d) * y         ∎

    2-induction : ∀ {ℓ} {P : Pred ℕ ℓ}
              → P 0
              → P 1
              → (∀ n → P n → P (suc n) → P (suc (suc n)))
              → (∀ n → P n)
    2-induction c₀ c₁ cₛ 0             = c₀
    2-induction c₀ c₁ cₛ 1             = c₁
    2-induction c₀ c₁ cₛ (suc (suc n)) = cₛ n (2-induction c₀ c₁ cₛ n)
                                            (2-induction c₀ c₁ cₛ (suc n))

    Lemma₁ : ∀ (n z : ℕ) → Set
    Lemma₁ zero      _ = ⊥
    Lemma₁ (suc n-1) z = let n = suc n-1 in
      f (1 + z + n) ≡ f (2 + z) * f n + f (1 + z) * f n-1

  lemma₁ : ∀ n → n > 0 → ∀ m → Lemma₁ n m
  lemma₁ zero      ()  _
  lemma₁ (suc n-1) n>0 m =
    let n = suc n-1
        case₀ : Lemma₁ n 0
        case₀ = begin
          f (1 + n)               ≡⟨⟩
          f n + f n-1             ≡⟨ +-cong (*-identityˡ (f n)) (*-identityˡ (f n-1)) ⟩
          1 * f n + 1 * f n-1     ≡⟨⟩
          f 2 * f n + f 1 * f n-1 ∎
        case₁ : Lemma₁ n 1
        case₁ = begin
          f (2 + n)               ≡⟨⟩
          f (1 + n) + f n         ≡⟨⟩
          f n + f n-1 + f n       ≡⟨ +-assoc (f n) (f n-1) (f n) ⟩
          f n + (f n-1 + f n)     ≡⟨ +-cong (xrefl (f n)) (+-comm (f n-1) (f n)) ⟩
          f n + (f n + f n-1)     ≡⟨ sym (+-assoc (f n) (f n) (f n-1)) ⟩
          f n + f n + f n-1       ≡⟨ +-cong (+-double (f n)) (*-identityˡ (f n-1)) ⟩
          2 * f n + 1 * f n-1     ≡⟨⟩
          f 3 * f n + f 2 * f n-1 ∎
        caseₛ : ∀ k → Lemma₁ n k → Lemma₁ n (1 + k) → Lemma₁ n (2 + k)
        caseₛ k c₀ c₁ = begin
          f (3 + k + n)                           ≡⟨⟩
          f (2 + k + n) + f (1 + k + n)           ≡⟨ +-cong c₁ c₀ ⟩
            (f (3 + k) * f n + f (2 + k) * f n-1)
          + (f (2 + k) * f n + f (1 + k) * f n-1) ≡⟨ axbycxdy (f (3 + k)) (f (2 + k)) (f (2 + k)) (f (1 + k)) (f n) (f n-1) ⟩
            (f (3 + k) + f (2 + k)) * f n
          + (f (2 + k) + f (1 + k)) * f n-1       ≡⟨⟩
          f (4 + k) * f n + f (3 + k) * f n-1     ∎
    in 2-induction case₀ case₁ caseₛ m
