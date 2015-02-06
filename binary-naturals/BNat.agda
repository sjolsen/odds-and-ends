module BNat where
  open import Data.Product
  open import Function
  open import Relation.Nullary
  open import Relation.Nullary.Negation
  open import Relation.Binary.PropositionalEquality

  open import BNat.Core
  open import BNat.Ordering
  open import BNat.Conversion

  _+₂_ : ∀ {i} → ℕ₂ {i} → ℕ₂ {i} → ℕ₂ {suc i}
  m +₂ n = add m n 0b
    where addb : Bit → Bit → Bit → Bit × Bit
          addb 0b 0b c  = (0b , c)
          addb 0b 1b 0b = (0b , 1b)
          addb 0b 1b 1b = (1b , 0b)
          addb 1b 0b 0b = (0b , 1b)
          addb 1b 0b 1b = (1b , 0b)
          addb 1b 1b c  = (1b , c)
          add : ∀ {i} → ℕ₂ {i} → ℕ₂ {i} → Bit → ℕ₂ {suc i}
          add (bit     m) (bit     n) c = uncurry′ bits $ map bit         id $ addb m n c
          add (bits ms m) (bits ns n) c = uncurry′ bits $ map (add ms ns) id $ addb m n c

  _-₂_ : ∀ {i} (m n : ℕ₂ {i}) → {m≮n : ¬ m <₂ n} → ℕ₂ {i}
  _-₂_ m n {m≮n} = sub m n 0b
    where subb : Bit → Bit → Bit → Bit × Bit
          subb 0b 0b c̄ = (c̄  , c̄)
          subb 0b 1b c̄ = (1b , not c̄)
          subb 1b 0b c̄ = (0b , not c̄)
          subb 1b 1b c̄ = (c̄  , c̄)
          sub : ∀ {i} → ℕ₂ {i} → ℕ₂ {i} → Bit → ℕ₂ {i}
          sub (bit     m) (bit     n) c̄ = bit $ proj₂ (subb m n c̄)
          sub (bits ms m) (bits ns n) c̄ = uncurry′ bits $ map (sub ms ns) id $ subb m n c̄


  Nonzero : ∀ {i} → ℕ₂ {i} → Set
  Nonzero n = ¬ n ≡ 0₂

  pred₂ : ∀ {i} (n : ℕ₂ {i}) {n≠0 : Nonzero n} → ℕ₂ {i}
  pred₂ (bit     0b) {n≠0} = contradiction refl n≠0
  pred₂ (bit     1b)       = bit 0b
  pred₂ (bits ns 0b) {n≠0} = bits (pred₂ ns {contraposition (λ ns=0 → cong₂ bits ns=0 refl) n≠0}) 1b
  pred₂ (bits ns 1b)       = bits ns 0b

  ⌈log₂_⌉ : ∀ {i} (n : ℕ₂ {i}) {_ : Nonzero n} → ℕ₂ {i}
  ⌈log₂ n ⌉ {n≠0} = len (pred₂ n {n≠0})
    where len : ∀ {i} → ℕ₂ {i} → ℕ₂ {i}
          len (bit     n) = bit n
          len (bits ns n) with len ns | n
          ... | bit 0b | 0b = 0₂
          ... | l′     | _  = l′ +₂ 1₂


  -- divmod : ∀ {i} (a b : ℕ₂ {i}) → {b≠0 : Nonzero b} → ℕ₂ {i} × ℕ₂ {i}
  -- divmod {i} a b = {!!}
  --   where lshft : ℕ₂ {i} → ℕ₂ {i}
  --         lshft x = {!!}
  --         loop₁ : ℕ₂ {i} × ℕ₂ {i} → ℕ₂ {i} × ℕ₂ {i}
  --         loop₁ (denom , scale) with denom <₂? a
  --         ... | yes _ = loop₁ ((lshft denom) , (lshft scale))
  --         ... | no  _ = denom , scale
