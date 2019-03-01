module Data.Fin.Subset.Cardinality where
  open import Data.Fin.Subset

  _∖_ : ∀ {n} → Subset n → Subset n → Subset n
  _∖_ {n} a b = a ∩ ∁ b

