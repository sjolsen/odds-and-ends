module BNat.Conversion where
  open import BNat.Core
  open import Function
  open import Data.Product
  open import Data.Nat    using (_+_; _*_)
  open import Data.List   using (List; []; _∷_) renaming (map to mapl)
  open import Data.Char   using (Char)
  open import Data.String using (String; fromList)

  fromℕ : ∀ {i} (n : ℕ) → ℕ₂ {i}
  fromℕ 0 = 0₂
  fromℕ 1 = 1₂
  fromℕ {zero}  (suc (suc n)) = fromℕ (suc n)
  fromℕ {suc i} n = uncurry′ bits $ map fromℕ id $ divmod₂ n
    where divmod₂ : ℕ → ℕ × Bit
          divmod₂ 0 = (0 , 0b)
          divmod₂ 1 = (0 , 1b)
          divmod₂ (suc (suc n)) = map suc id $ divmod₂ n

  bitToℕ : Bit → ℕ
  bitToℕ 0b = 0
  bitToℕ 1b = 1

  toℕ : ∀ {i} → ℕ₂ {i} → ℕ
  toℕ (bit     n) = bitToℕ n
  toℕ (bits ns n) = 2 * toℕ ns + bitToℕ n

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
