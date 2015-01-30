module PlusReasoning where
  open import Data.Nat
  open import Data.Empty
  open import Relation.Nullary
  open import Relation.Nullary.Negation
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans) public

  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

  0+a=a : ∀ {a} → 0 + a ≡ a
  0+a=a = refl

  a+0=a : ∀ {a} → a + 0 ≡ a
  a+0=a {zero}  = refl
  a+0=a {suc a} = cong suc a+0=a

  +-comm : ∀ {a b} → a + b ≡ b + a
  +-comm {zero}  {b}     = trans 0+a=a (sym a+0=a)
  +-comm {suc a} {zero}  = trans a+0=a (sym 0+a=a)
  +-comm {suc a} {suc b} with +-comm {a} {suc b} | +-comm {b} {suc a}
  ... | a+1+b | b+1+a = cong suc (trans a+1+b (sym (trans b+1+a (cong suc (+-comm {a} {b})))))

  ≡→≤ : ∀ {a b} → a ≡ b → a ≤ b
  ≡→≤ {zero}            a=b = z≤n
  ≡→≤ {suc a′} {zero}   a=b = contradiction a=b (λ ())
  ≡→≤ {suc a′} {suc b′} a=b = s≤s (≡→≤ (suc-inj a=b))

  ≤-subst₁ : ∀ {a b c} → a ≤ b → a ≡ c → c ≤ b
  ≤-subst₁ {zero}   {c = zero}   a≤b a=c = a≤b
  ≤-subst₁ {zero}   {c = suc c′} a≤b a=c = contradiction a=c (λ ())
  ≤-subst₁ {suc a′} {c = zero}   a≤b a=c = contradiction a=c (λ ())
  ≤-subst₁ {suc a′} {c = suc c′} a≤b a=c = ≤-trans (≡→≤ (sym a=c)) a≤b

  ≤-subst₂ : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
  ≤-subst₂ {zero} a≤b b=c = z≤n
  ≤-subst₂ {suc a} {b} {c} a′≤b b=c = ≤-trans a′≤b (≡→≤ b=c)

  a≤a+b : ∀ {a b} → a ≤ a + b
  a≤a+b {zero}  = z≤n
  a≤a+b {suc a} = s≤s a≤a+b

  b≤a+b : ∀ {a b} → b ≤ a + b
  b≤a+b {a} {b} = ≤-subst₂ a≤a+b (+-comm {b} {a})


  triangle : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
  triangle {zero}   {b}      {d = d} a≤b c≤d = ≤-trans c≤d (b≤a+b {b} {d})
  triangle {suc a′} {zero}           a≤b c≤d = contradiction a≤b (λ ())
  triangle {suc a′} {suc b′} (s≤s a′≤b′) c≤d = s≤s (triangle a′≤b′ c≤d)
