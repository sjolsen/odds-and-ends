module Lucas where
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
  open SemiringSolver

  f : ℕ → ℕ
  f 0 = 0
  f 1 = 1
  f (suc (suc n)) = f (suc n) + f n

  l : ℕ → ℕ
  l 0 = 2
  l 1 = 1
  l (suc (suc n)) = l (suc n) + l n



  private
    +-cong = cong₂ _+_

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

    [ab][cd]⇒[ac][bd] : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
    [ab][cd]⇒[ac][bd] = solve 4 (λ a b c d → a :+ b :+ (c :+ d) := a :+ c :+ (b :+ d)) refl


  Lemma-11a : ∀ (n-1 : ℕ) → Set
  Lemma-11a n-1 = let n = suc n-1 in l n ≡ f n-1 + f (1 + n)

  proof-11a : ∀ n-1 → Lemma-11a n-1
  proof-11a = 2-induction case₀ case₁ caseₛ
    where case₀ : Lemma-11a 0
          case₀ = begin
            l 1       ≡⟨⟩
            1         ≡⟨⟩
            0 + 1     ≡⟨⟩
            f 0 + f 2 ∎
          case₁ : Lemma-11a 1
          case₁ = begin
            l 2       ≡⟨⟩
            3         ≡⟨⟩
            1 + 2     ≡⟨⟩
            f 1 + f 3 ∎
          caseₛ : ∀ n
                → Lemma-11a n
                → Lemma-11a (1 + n)
                → Lemma-11a (2 + n)
          caseₛ n c₀ c₁ = begin
            l (3 + n)                                   ≡⟨⟩
            l (2 + n) + l (1 + n)                       ≡⟨ +-cong c₁ c₀ ⟩
            (f (1 + n) + f (3 + n)) + (f n + f (2 + n)) ≡⟨ [ab][cd]⇒[ac][bd] (f (1 + n)) (f (3 + n)) (f n) (f (2 + n)) ⟩
            (f (1 + n) + f n) + (f (3 + n) + f (2 + n)) ≡⟨⟩
            f (2 + n) + f (4 + n)                       ∎


  private
    inclusive-sum : ℕ → (ℕ → ℕ) → ℕ
    inclusive-sum 0       f = f 0
    inclusive-sum (suc n) f = (inclusive-sum n f) + f (suc n)

  Lemma-11b : ∀ (n : ℕ) → Set
  Lemma-11b n = inclusive-sum n (λ i → l i * l i) ≡ l n * l (suc n) + 2

  proof-11b : ∀ n → Lemma-11b n
  proof-11b = 1-induction case₀ caseₛ
    where case₀ : Lemma-11b 0
          case₀ = begin
            inclusive-sum 0 (λ i → l i * l i) ≡⟨⟩
            l 0 * l 0                         ≡⟨⟩
            2 * 2                             ≡⟨⟩
            4                                 ≡⟨⟩
            2 + 2                             ≡⟨⟩
            2 * 1 + 2                         ≡⟨⟩
            l 0 * l 1 + 2                     ∎
          caseₛ : ∀ n-1 → Lemma-11b n-1 → Lemma-11b (suc n-1)
          caseₛ n-1 cₙ = let n = suc n-1 in begin
            inclusive-sum n   (λ i → l i * l i)             ≡⟨⟩
            inclusive-sum n-1 (λ i → l i * l i) + l n * l n ≡⟨ +-cong cₙ refl ⟩
            l n-1 * l n + 2 + l n * l n                     ≡⟨ solve 3 (λ a b c → a :* b :+ c :+ b :* b := a :* b :+ b :* b :+ c) refl (l n-1) (l n) 2 ⟩
            l n-1 * l n + l n * l n + 2                     ≡⟨ +-cong (sym $ distribʳ-*-+ (l n) (l n-1) (l n)) refl ⟩
            (l n-1 + l n) * l n + 2                         ≡⟨ solve 3 (λ a b c → (a :+ b) :* b :+ c := b :* (b :+ a) :+ c) refl (l n-1) (l n) 2 ⟩
            l n * (l n + l n-1) + 2                         ≡⟨⟩
            l n * l (suc n) + 2                             ∎
