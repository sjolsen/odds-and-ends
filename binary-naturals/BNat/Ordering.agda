module BNat.Ordering where
  open import BNat.Core
  open import Level
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Negation

  -- Ordering based on strict less-than relation

  data bit-< : Rel Bit Level.zero where
    0<1 : bit-< 0b 1b

  data _<₂_ : ∀ {i} → Rel (ℕ₂ {i}) Level.zero where
    0<1   : ∀ {m n}                     → bit-< m n → bit m <₂ bit n
    *0<*1 : ∀ {i ms m ns n} → ms ≡ ns   → bit-< m n → bits {i} ms m <₂ bits {i} ns n
    0*<1* : ∀ {i ms m ns n} → ms <₂ ns              → bits {i} ms m <₂ bits {i} ns n

  -- Decidable ordering

  bit-<? : Relation.Binary.Decidable bit-<
  bit-<? 0b 0b = no (λ ())
  bit-<? 0b 1b = yes 0<1
  bit-<? 1b 0b = no (λ ())
  bit-<? 1b 1b = no (λ ())

  private
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
