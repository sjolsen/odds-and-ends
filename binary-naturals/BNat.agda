{-# OPTIONS --sized-types #-}
module BNat where
  import Level
  open import Data.Nat
  open import Data.Sum hiding (map)
  open import Data.Product
  open import Function
  open import Data.Empty
  open import Relation.Nullary
  open import Relation.Nullary.Decidable hiding (map)
  open import Relation.Nullary.Negation
  open import Relation.Unary
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Data.String using (String; fromList)
  open import Data.List renaming (map to mapl)
  open import Data.Char hiding (show)
  open import PlusReasoning

  data Bit : Set where
    0b : Bit
    1b : Bit

  data ℕ₂ : {i : ℕ} → Set where
    bit  :                       Bit → ℕ₂ {zero}
    bits : ∀ {i : ℕ} → ℕ₂ {i} → Bit → ℕ₂ {suc i}

  0₂ : ∀ {i} → ℕ₂ {i}
  0₂ {zero}  = bit 0b
  0₂ {suc n} = bits 0₂ 0b

  1₂ : ∀ {i} → ℕ₂ {i}
  1₂ {zero}  = bit 1b
  1₂ {suc n} = bits 0₂ 1b

  not : Bit → Bit
  not 0b = 1b
  not 1b = 0b


  fromℕ : ∀ {i} (n : ℕ) → ℕ₂ {i}
  fromℕ 0 = 0₂
  fromℕ 1 = 1₂
  fromℕ {zero}  (suc (suc n)) = fromℕ (suc n)
  fromℕ {suc i} n = uncurry′ bits $ map fromℕ id $ divmod₂ n
    where divmod₂ : ℕ → ℕ × Bit
          divmod₂ 0 = (0 , 0b)
          divmod₂ 1 = (0 , 1b)
          divmod₂ (suc (suc n)) = map suc id $ divmod₂ n


  showBit : Bit → Char
  showBit 0b = '0'
  showBit 1b = '1'

  show : ∀ {i} → ℕ₂ {i} → String
  show = fromList ∘ mapl showBit ∘ flip showl []
    where showl : ∀ {i} → ℕ₂ {i} → List Bit → List Bit
          showl (bit 0b)    []  = 0b ∷ []
          showl (bit 0b)    acc = acc
          showl (bit 1b)    acc = 1b ∷ acc
          showl (bits ns n) acc = showl ns (n ∷ acc)


  bit-eq? : Relation.Binary.Decidable {A = Bit} _≡_
  bit-eq? 0b 0b = yes refl
  bit-eq? 0b 1b = no (λ ())
  bit-eq? 1b 0b = no (λ ())
  bit-eq? 1b 1b = yes refl

  bit-injective : ∀ {m n} → bit m ≡ bit n → m ≡ n
  bit-injective refl = refl

  bits-injective₁ : ∀ {i ms m ns n} → bits {i} ms m ≡ bits {i} ns n → ms ≡ ns
  bits-injective₁ refl = refl

  bits-injective₂ : ∀ {i ms m ns n} → bits {i} ms m ≡ bits {i} ns n → m ≡ n
  bits-injective₂ refl = refl

  _≟₂_ : ∀ {i} → Relation.Binary.Decidable {A = ℕ₂ {i}} _≡_
  bit m ≟₂ bit n with bit-eq? m n
  ... | yes m=n = yes (cong bit m=n)
  ... | no  m≠n = no  (contraposition bit-injective m≠n)
  bits ms m ≟₂ bits ns n with ms ≟₂ ns | bit-eq? m n
  ... | yes ms=ns | yes m=n = yes (cong₂ bits ms=ns m=n)
  ... | no  ms≠ns | _       = no  (contraposition bits-injective₁ ms≠ns)
  ... | _         | no  m≠n = no  (contraposition bits-injective₂ m≠n)


  data bit-< : Rel Bit Level.zero where
    0<1 : bit-< 0b 1b

  bit-<? : Relation.Binary.Decidable bit-<
  bit-<? 0b 0b = no (λ ())
  bit-<? 0b 1b = yes 0<1
  bit-<? 1b 0b = no (λ ())
  bit-<? 1b 1b = no (λ ())

  data _<₂_ : ∀ {i} → Rel (ℕ₂ {i}) Level.zero where
    0<1   : ∀ {m n}                     → bit-< m n → bit m <₂ bit n
    *0<*1 : ∀ {i ms m ns n} → ms ≡ ns   → bit-< m n → bits {i} ms m <₂ bits {i} ns n
    0*<1* : ∀ {i ms m ns n} → ms <₂ ns              → bits {i} ms m <₂ bits {i} ns n

  0<1-elim : ∀ {m n} → bit m <₂ bit n → bit-< m n
  0<1-elim (0<1 m<n) = m<n

  _<₂?_ : ∀ {i} → Relation.Binary.Decidable (_<₂_ {i})
  bit m <₂? bit n with bit-<? m n
  ... | yes m=n = yes (0<1 m=n)
  ... | no  m≠n = no (contraposition 0<1-elim m≠n)
  bits ms m  <₂? bits ns n with ms <₂? ns | ms ≟₂ ns | bit-<? m n
  ... | yes ms<ns | _         | _       = yes (0*<1* ms<ns)
  ... | _         | yes ms=ns | yes m<n = yes (*0<*1 ms=ns m<n)
  ... | no  ms≮ns | yes ms=ns | no  m≮n = no absurd
    where absurd : ¬ bits ms m <₂ bits ns n
          absurd (*0<*1 ms=ns m<n) = contradiction m<n m≮n
          absurd (0*<1* ms<ns)     = contradiction ms<ns ms≮ns
  ... | no  ms≮ns | no  ms≠ns | _       = no absurd
    where absurd : ¬ bits ms m <₂ bits ns n
          absurd (*0<*1 ms=ns m<n) = contradiction ms=ns ms≠ns
          absurd (0*<1* ms<ns)     = contradiction ms<ns ms≮ns

  _≤₂_ : ∀ {i} → Rel (ℕ₂ {i}) Level.zero
  m ≤₂ n = m <₂ n ⊎ m ≡ n


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


  data zerop : ∀ {i} → Pred (ℕ₂ {i}) Level.zero where
    zerop₀ :                           zerop (bit     0b)
    zerop₁ : ∀ {i ns} → zerop {i} ns → zerop (bits ns 0b)

  zerop-elim : ∀ {i ns} → zerop {suc i} (bits ns 0b) → zerop {i} ns
  zerop-elim (zerop₁ ns=0) = ns=0

  zero? : ∀ {i} → Relation.Unary.Decidable (zerop {i})
  zero? (bit 0b) = yes zerop₀
  zero? (bit 1b) = no (λ ())
  zero? (bits ns n) with zero? ns | n
  ... | yes ns=0 | 0b = yes (zerop₁ ns=0)
  ... | yes ns=0 | 1b = no (λ ())
  ... | no  ns≠0 | 1b = no (λ ())
  ... | no  ns≠0 | 0b = no (contraposition zerop-elim ns≠0)

  Nonzero : ∀ {i} → ℕ₂ {i} → Set
  Nonzero n = ¬ zerop n

  pred₂ : ∀ {i} (n : ℕ₂ {i}) {n≠0 : Nonzero n} → ℕ₂ {i}
  pred₂ (bit     0b) {n≠0} = contradiction zerop₀ n≠0
  pred₂ (bit     1b)       = bit 0b
  pred₂ (bits ns 0b) {n≠0} = bits (pred₂ ns {contraposition zerop₁ n≠0}) 1b
  pred₂ (bits ns 1b)       = bits ns 0b

  ⌈log₂_⌉ : ∀ {i} (n : ℕ₂ {i}) {_ : ¬ zerop n} → ℕ₂ {i}
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

  ten = bits (bits (bits (bit 1b) 0b) 1b) 0b
  seven = bits (bits (bits (bit 0b) 1b) 1b) 1b
  three = ten -₂ seven
