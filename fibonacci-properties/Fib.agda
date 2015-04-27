module Fib where
  open import Data.Empty
  open import Data.Nat
  open import Data.Nat.Divisibility renaming (poset to ∣-poset) hiding (*-cong)
  open import Data.Nat.Properties
  open import Data.Nat.Properties.Simple
  open import Relation.Unary
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Function
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

    abc≡acb : ∀ a b c → a + b + c ≡ a + c + b
    abc≡acb a b c = begin
      (a + b) + c ≡⟨ +-assoc a b c ⟩
      a + (b + c) ≡⟨ +-cong (xrefl a) (+-comm b c) ⟩
      a + (c + b) ≡⟨ sym $ +-assoc a c b ⟩
      (a + c) + b ∎

    1-induction : ∀ {ℓ} {P : Pred ℕ ℓ}
              → P 0
              → (∀ n → P n → P (suc n))
              → (∀ n → P n)
    1-induction c₀ cₛ 0       = c₀
    1-induction c₀ cₛ (suc n) = cₛ n (1-induction c₀ cₛ n)

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
                f n +       f n-1 ≡⟨ +-cong (*-identityˡ (f n)) (*-identityˡ (f n-1)) ⟩
            1 * f n +   1 * f n-1 ≡⟨⟩
          f 2 * f n + f 1 * f n-1 ∎
        case₁ : Lemma₁ n 1
        case₁ = begin
          f (2 + n)                 ≡⟨⟩
          f (1 + n)   +       f n   ≡⟨⟩
          f n + f n-1 +       f n   ≡⟨ abc≡acb (f n) (f n-1) (f n) ⟩
          f n + f n   +       f n-1 ≡⟨ +-cong (+-double (f n)) (*-identityˡ (f n-1)) ⟩
            2 * f n   +   1 * f n-1 ≡⟨⟩
          f 3 * f n   + f 2 * f n-1 ∎
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


  private
    0*n : ∀ n → 0 * n ≡ 0
    0*n n = refl
    n*0 : ∀ n → n * 0 ≡ 0
    n*0 n = subst₂ _≡_ (*-comm zero n) refl (0*n n)

    ≡→∣ : ∀ {m n} → m ≡ n → m ∣ n
    ≡→∣ = Poset.reflexive ∣-poset

    Lemma₂ : ∀ n p → Set
    Lemma₂ n p = f n ∣ f (p * n)

  lemma₂ : ∀ n m → n ∣ m → f n ∣ f m
  lemma₂ 0 m (divides p m≡p*n) = ≡→∣ $ begin
    f 0       ≡⟨ cong f $ sym (n*0 p) ⟩
    f (p * 0) ≡⟨ cong f $ sym m≡p*n ⟩
    f m       ∎
  lemma₂ (suc n-1) m (divides p m≡p*n) =
    subst₂ _∣_ refl (sym (cong f m≡p*n)) (1-induction case₀ caseₛ p)
      where n = suc n-1
            case₀ : Lemma₂ n 0
            case₀ = f n ∣0
            case₁ : Lemma₂ n 1
            case₁ = ≡→∣ $ begin
              f n       ≡⟨ cong f (*-identityˡ n) ⟩
              f (1 * n) ∎
            caseₙ : ∀ p-2 → Lemma₂ n (suc p-2) → Lemma₂ n (suc (suc p-2))
            caseₙ p-2 (divides q f[[p-1]n]≡q*fn) =
              let p-1 = suc p-2
                  p   = suc p-1
                  z   = p-2 * n + n-1
              in divides (f (2 + z) + q * f n-1) $
              begin
                f (p * n) ≡⟨ cong f $
                begin
                  p * n                   ≡⟨⟩
                  n + (n + p-2 * n)       ≡⟨ +-cong (xrefl n) (+-comm n (p-2 * n)) ⟩
                  n + (p-2 * n + n)       ≡⟨ sym $ +-assoc n (p-2 * n) n ⟩
                  n + p-2 * n + n         ≡⟨⟩
                  (1 + n-1) + p-2 * n + n ≡⟨ +-cong (+-assoc 1 n-1 (p-2 * n)) refl ⟩
                  1 + (n-1 + p-2 * n) + n ≡⟨ +-cong (+-cong (xrefl 1) (+-comm n-1 (p-2 * n))) refl ⟩
                  1 + (p-2 * n + n-1) + n ≡⟨⟩
                  1 + z + n
                ∎ ⟩
                f (1 + z + n)                       ≡⟨ lemma₁ n (s≤s z≤n) z ⟩
                f (2 + z) * f n + f (1 + z) * f n-1 ≡⟨ +-cong (xrefl (f (2 + z) * f n)) $
                begin
                  f (1 + z) * f n-1               ≡⟨⟩
                  f (1 + (p-2 * n + n-1)) * f n-1 ≡⟨ flip *-cong refl $ cong f $
                  begin
                    1 + (p-2 * n + n-1) ≡⟨ +-comm 1 (p-2 * n + n-1) ⟩
                    p-2 * n + n-1 + 1   ≡⟨ +-assoc (p-2 * n) n-1 1 ⟩
                    p-2 * n + (n-1 + 1) ≡⟨ +-cong (xrefl (p-2 * n)) (+-comm n-1 1) ⟩
                    p-2 * n + (1 + n-1) ≡⟨ +-comm (p-2 * n) n ⟩
                    n + p-2 * n         ≡⟨⟩
                    p-1 * n
                  ∎ ⟩
                  f (p-1 * n) * f n-1 ≡⟨ *-cong f[[p-1]n]≡q*fn refl ⟩
                  (q * f n) * f n-1   ≡⟨ *-assoc q (f n) (f n-1) ⟩
                  q * (f n * f n-1)   ≡⟨ *-cong (xrefl q) (*-comm (f n) (f n-1)) ⟩
                  q * (f n-1 * f n)   ≡⟨ sym $ *-assoc q (f n-1) (f n) ⟩
                  (q * f n-1) * f n
                ∎ ⟩
                f (2 + z) * f n + (q * f n-1) * f n ≡⟨ sym $ distribʳ-*-+ (f n) (f (2 + z)) (q * f n-1) ⟩
                (f (2 + z) + q * f n-1) * f n
              ∎
            caseₛ : ∀ p → Lemma₂ n p → Lemma₂ n (suc p)
            caseₛ 0 _         = case₁
            caseₛ (suc p-1) x = caseₙ p-1 x
