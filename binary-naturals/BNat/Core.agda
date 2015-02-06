module BNat.Core where
  open import Data.Nat using (ℕ; zero; suc) public
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Negation

  -- Base definitions

  data Bit : Set where
    0b : Bit
    1b : Bit

  data ℕ₂ : {i : ℕ} → Set where
    bit  :                      Bit → ℕ₂ {zero}
    bits : ∀ {i : ℕ} → ℕ₂ {i} → Bit → ℕ₂ {suc i}

  bit-injective : ∀ {m n} → bit m ≡ bit n → m ≡ n
  bit-injective refl = refl

  bits-injective₁ : ∀ {i ms m ns n} → bits {i} ms m ≡ bits {i} ns n → ms ≡ ns
  bits-injective₁ refl = refl

  bits-injective₂ : ∀ {i ms m ns n} → bits {i} ms m ≡ bits {i} ns n → m ≡ n
  bits-injective₂ refl = refl

  -- Decidable propositional equality

  bit-eq? : Decidable {A = Bit} _≡_
  bit-eq? 0b 0b = yes refl
  bit-eq? 0b 1b = no (λ ())
  bit-eq? 1b 0b = no (λ ())
  bit-eq? 1b 1b = yes refl

  _≟₂_ : ∀ {i} → Relation.Binary.Decidable {A = ℕ₂ {i}} _≡_
  bit m ≟₂ bit n with bit-eq? m n
  ... | yes m=n = yes (cong bit m=n)
  ... | no  m≠n = no  (contraposition bit-injective m≠n)
  bits ms m ≟₂ bits ns n with ms ≟₂ ns | bit-eq? m n
  ... | yes ms=ns | yes m=n = yes (cong₂ bits ms=ns m=n)
  ... | no  ms≠ns | _       = no  (contraposition bits-injective₁ ms≠ns)
  ... | _         | no  m≠n = no  (contraposition bits-injective₂ m≠n)

  -- Basic utilities

  not : Bit → Bit
  not 0b = 1b
  not 1b = 0b

  0₂ : ∀ {i} → ℕ₂ {i}
  0₂ {zero}  = bit 0b
  0₂ {suc n} = bits 0₂ 0b

  1₂ : ∀ {i} → ℕ₂ {i}
  1₂ {zero}  = bit 1b
  1₂ {suc n} = bits 0₂ 1b
