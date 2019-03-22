module Data.Finitary.Exponent where
open import Data.Finitary
open import Data.Fin as Fin using (Fin; toℕ)
open import Data.Nat
open import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality as P
open import Data.Nat.DivMod
open import Relation.Nullary.Decidable
open import Function
open import Function.Equality as F using (_⟶_; _⟨$⟩_; _⇨_) 
open import Function.Inverse as Inv using (module Inverse; Inverse)
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Relation.Binary

exponent : ∀ {m} {n} → Finitary (P.setoid (Vec (Fin m) n)) (m ^ n)
exponent {m} {n} = record {
    to = P.→-to-⟶ to
  ; from = P.→-to-⟶ from
  ; inverse-of = record {
      left-inverse-of = from∘to
    ; right-inverse-of = to∘from {m}{n}
    }
  }
  where
    open import Data.Nat.Properties 
    open import Data.Fin.Properties hiding (≤-refl; _≟_; <-cmp)
    open import Relation.Nullary.Negation 
    shift : ∀ {m n} (i : Fin m)(j : Fin n) → toℕ j + (toℕ i) * n < m * n
    shift {m}{n} i j =
              begin suc (toℕ j) + toℕ i * n  
                ≤⟨ +-mono-≤ (toℕ<n j) (≤-refl {(toℕ i) * n}) ⟩
                  n + toℕ i * n 
                ≤⟨ *-mono-≤ (toℕ<n i) ≤-refl ⟩ m * n ∎ 
          where
            open ≤-Reasoning
    to : ∀ {m n} → Vec (Fin m) n → Fin (m ^ n)
    to [] = Fin.zero
    to {m}{n = suc n} (i ∷ is) = Fin.fromℕ≤ (shift i (to is))

    suci^j≢0  : ∀ i j → suc i ^ j ≢ 0
    suci^j≢0 i j eq with i^j≡0⇒i≡0 _ j eq
    ... | ()

    from : ∀ {m n} → Fin (m ^ n) → Vec (Fin m) n
    from {m} {zero} i = []
    from {zero} {suc n} ()
    from {suc m} {suc n} i with ((toℕ i) divMod (suc m ^ n))
      {≢0 = fromWitnessFalse (suci^j≢0 _ n)} 
    from {suc m} {suc n} i | result quotient remainder property
      = Fin.fromℕ≤ q<sm  ∷ from remainder
      where
        q<sm : quotient < suc m
        q<sm = ≰⇒> (λ sm≤q → <⇒≱ (toℕ<n i)
                (begin (suc m) * (suc m ^ n)
                   ≤⟨ *-mono-≤ sm≤q ≤-refl ⟩ quotient * (suc m ^ n)
                   ≤⟨ +-mono-≤ (z≤n {toℕ remainder}) ≤-refl ⟩ toℕ remainder + quotient * (suc m ^ n)
                   ≡⟨ P.sym property ⟩ toℕ i ∎)) 
              where
                open ≤-Reasoning 
    ≢→<⊎> : ∀ {m n} → m ≢ n → m < n ⊎ n < m
    ≢→<⊎> {m}{n} m≢n  with <-cmp m n
    ≢→<⊎> {m} {n} m≢n | tri<  m<n _ _ = inj₁ m<n
    ≢→<⊎> {m} {n} m≢n | tri≈ _ m≡n _ = ⊥-elim (m≢n m≡n)
    ≢→<⊎> {m} {n} m≢n | tri> _ _ n<m = inj₂ n<m

    chn : ∀ m → ∀ {k₀ k₁} {r₀ r₁ : Fin m} → toℕ r₀ + k₀ * m  ≡ toℕ r₁ + k₁ * m → k₀ ≡ k₁ × r₀ ≡ r₁
    chn zero {k₀} {k₁} {()} {r₁} _ 
    chn (suc m) {k₀} {k₁} {r₀} {r₁} eq = k₀≡k₁ , r₀≡r₁
      where
        open ≤-Reasoning    
        contra : k₀ ≢ k₁ → ⊥
        contra k₀≢k₁ with ≢→<⊎> k₀≢k₁
        ... | inj₁ k₀<k₁ = <⇒≱  (toℕ<n r₀) (+-cancelʳ-≤ (suc m) (toℕ r₀)
                                 (begin suc m + k₀ * suc m
                                   ≡⟨ refl ⟩ suc k₀ * suc m
                                   ≤⟨ *-mono-≤ (m≤m+n (suc k₀) (k₁ ∸ suc k₀)) (≤-refl {suc m}) ⟩
                                          (suc k₀ + (k₁ ∸ suc k₀)) * suc m
                                   ≡⟨ P.cong₂ _*_ (m+n∸m≡n k₀<k₁) refl ⟩ k₁ * suc m
                                   ≤⟨ n≤m+n (toℕ r₁) (k₁ * suc m)  ⟩ toℕ r₁ + k₁ * suc m
                                   ≡⟨ P.sym eq ⟩ toℕ r₀ + k₀ * suc m ∎))
        ... | inj₂ k₁<k₀ = <⇒≱  (toℕ<n r₁) (+-cancelʳ-≤  (suc m) (toℕ r₁)
                  (begin suc k₁ * suc m
                         ≤⟨ *-mono-≤ (m≤m+n (suc k₁) (k₀ ∸ suc k₁)) (≤-refl {suc m}) ⟩
                         (suc k₁ + (k₀ ∸ suc k₁)) * suc m
                         ≡⟨ P.cong₂ _*_ (m+n∸m≡n k₁<k₀) refl ⟩ k₀ * suc m
                         ≤⟨ n≤m+n  (toℕ r₀) (k₀ * suc m) ⟩ toℕ r₀ + k₀ * suc m 
                         ≡⟨ eq ⟩ toℕ r₁ + k₁ * suc m  ∎ )) 
        k₀≡k₁ : k₀ ≡ k₁
        k₀≡k₁ = decidable-stable (k₀ ≟ k₁) contra

        r₀≡r₁ : r₀ ≡ r₁
        r₀≡r₁ = toℕ-injective (+-cancelʳ-≡ (toℕ r₀) (toℕ r₁)
          (P.subst (λ k → toℕ r₀ + k * (suc m)  ≡ toℕ r₁ + k₁ * (suc m)) k₀≡k₁ eq))
        
    from∘to : ∀ {m n}(is : Vec (Fin m) n) → from (to is) ≡ is
    from∘to {m} {.0} [] = P.refl
    from∘to {zero} {.(suc _)} (() ∷ is)
    from∘to {suc m} {suc n} (i ∷ is) with to (i ∷ is) | P.inspect to (i ∷ is)
    from∘to {suc m} {suc n} (i ∷ is) | j | Reveal_·_is_.[ eq ] with P.cong toℕ eq
    ... | eq2 rewrite toℕ-fromℕ≤ (shift i (to is)) with ((toℕ j) divMod (suc m ^ n))
      {≢0 = fromWitnessFalse (suci^j≢0 _ n)}
    ... | result quotient remainder property with chn (suc m ^ n) {toℕ i}{quotient}
          {to is}{remainder} (trans eq2 property)
    ... | k₀≡k₁ , r₀≡r₁ rewrite P.sym r₀≡r₁ | from∘to is = 
        P.cong (_∷ is) (toℕ-injective (begin toℕ (Fin.fromℕ≤ _)
                                               ≡⟨ toℕ-fromℕ≤ _ ⟩ quotient
                                               ≡⟨ P.sym k₀≡k₁ ⟩ toℕ i ∎)) 
        where
          open ≡-Reasoning
    
    to∘from : ∀ {m n}(i : Fin (m ^ n)) → to (from{m}{n} i) ≡ i
    to∘from {m} {zero} Fin.zero = refl
    to∘from {m} {zero} (Fin.suc ())
    to∘from {zero} {suc n} ()
    to∘from {suc m} {suc n} i with ((toℕ i) divMod (suc m ^ n))
      {≢0 = fromWitnessFalse (suci^j≢0 _ n)}
    to∘from {suc m} {suc n} i | result quotient remainder property = goal
      where
        q<sm : quotient < suc m
        q<sm = ≰⇒> (λ sm≤q → <⇒≱ (toℕ<n i)
                (begin (suc m) * (suc m ^ n)
                   ≤⟨ *-mono-≤ sm≤q ≤-refl ⟩ quotient * (suc m ^ n)
                   ≤⟨ +-mono-≤ (z≤n {toℕ remainder}) ≤-refl ⟩ toℕ remainder + quotient * (suc m ^ n)
                   ≡⟨ P.sym property ⟩ toℕ i ∎)) 
              where
                open ≤-Reasoning 

        goal : to (Fin.fromℕ≤ q<sm  ∷ from {suc m}{n} remainder) ≡ i
        goal = toℕ-injective
              (begin _ ≡⟨ toℕ-fromℕ≤ _ ⟩
                         toℕ (to (from {suc m} {n} remainder)) + toℕ (Fin.fromℕ≤ q<sm ) * (suc m ^ n)
                       ≡⟨ P.cong₂ (λ r k → toℕ r + k * (suc m ^ n))
                            (to∘from {suc m} {n} remainder) (toℕ-fromℕ≤ q<sm)
                          ⟩  toℕ remainder + quotient * (suc m ^ n)
                       ≡⟨ P.sym property ⟩ toℕ i ∎)
          where
            open ≡-Reasoning
      

⟶-finitary-toVec : ∀{m n a b p q}{A : Setoid a p}{B : Setoid b q} → Finitary A m → Finitary B n
             → A ⟶ B → Vec (Fin n) m
⟶-finitary-toVec finA finB f = Vec.tabulate
                                   (λ i → (Inverse.to finB  F.∘ f F.∘ Inverse.from finA) ⟨$⟩ i )
                                   
             
⟶-finitary-fromVec : ∀{m n a b p q}{A : Setoid a p}{B : Setoid b q} → Finitary A m → Finitary B n
             → Vec (Fin n) m → A ⟶ B
⟶-finitary-fromVec {A = SA}{B = SB} finA finB vec =
  record {   _⟨$⟩_ = f
          ;  cong  = f-cong   }
  where
    open module SA = Setoid SA renaming (Carrier to A) using ()
    open module SB = Setoid SB renaming (Carrier to B) using ()    
    f : A → B
    f x = Inverse.from finB ⟨$⟩ Vec.lookup (Inverse.to finA ⟨$⟩ x) vec

    f-cong : ∀ {x y} → x SA.≈ y → f x SB.≈ f y
    f-cong {x}{y} x≈y = F.cong (Inverse.from finB)
                           (P.cong (flip Vec.lookup vec) (F.cong (Inverse.to finA) x≈y))
                       
        
⟶-finitary↔Vec : ∀{m n a b p q}{A : Setoid a p}{B : Setoid b q} → Finitary A n → Finitary B m
                 → Inverse (A ⇨ B) (P.setoid (Vec (Fin m) n))
Inverse.to (⟶-finitary↔Vec {m} {n} {A = S₁} {S₂} finA finB) ._⟨$⟩_ = ⟶-finitary-toVec finA finB
Inverse.to (⟶-finitary↔Vec {m} {n} {A = S₁} {S₂} finA finB) .F.cong {f} {g} eq = tabulate-cong ( λ i →
  F.cong (Inverse.to finB) (eq ≈₁-refl) )
  where
    open import Data.Vec.Properties 
    open Setoid S₁ renaming (isEquivalence to isEquivalence₁)
    open IsEquivalence isEquivalence₁ renaming (refl to ≈₁-refl)

Inverse.from (⟶-finitary↔Vec finA finB) = P.→-to-⟶ (⟶-finitary-fromVec finA finB)
Inv._InverseOf_.left-inverse-of (Inverse.inverse-of (⟶-finitary↔Vec {m = m}{n}{A = S₁} {S₂} finA finB)) f {x}{y} x≈y = 
  begin ⟶-finitary-fromVec finA finB (⟶-finitary-toVec finA finB f) ⟨$⟩ x
         ≈⟨ F.cong (Inverse.from finB) lemma  ⟩ _
         ≈⟨ linv₂ _  ⟩ _
         ≈⟨ F.cong f (linv₁ x) ⟩ _
         ≈⟨ F.cong f x≈y ⟩ f ⟨$⟩ y ∎
  where
    open import Data.Vec.Properties
    open import Relation.Binary.Reasoning.Setoid (S₂)
    open Setoid S₁ renaming (isEquivalence to isEquivalence₁)
    open IsEquivalence isEquivalence₁ renaming (refl to ≈₁-refl; trans to ≈₁-trans)
    open Setoid S₂ renaming (isEquivalence to isEquivalence₂)
    open IsEquivalence isEquivalence₂ renaming (refl to ≈₂-refl; trans to ≈₂-trans)
    F = (Inverse.to finB  F.∘ f F.∘ Inverse.from finA) ⟨$⟩_
    lemma = lookup∘tabulate F (Inverse.to finA ⟨$⟩ x)
    linv₁ = finA .Inverse.inverse-of .Inv._InverseOf_.left-inverse-of
    linv₂ = finB .Inverse.inverse-of .Inv._InverseOf_.left-inverse-of
Inv._InverseOf_.right-inverse-of (Inverse.inverse-of (⟶-finitary↔Vec finA finB)) vec =
  begin _  ≡⟨ tabulate-cong lemma ⟩ _ 
           ≡⟨ tabulate∘lookup vec ⟩ vec ∎
  where
    open import Data.Vec.Properties
    open P.≡-Reasoning
    rinv₁ = finA .Inverse.inverse-of .Inv._InverseOf_.right-inverse-of
    rinv₂ = finB .Inverse.inverse-of .Inv._InverseOf_.right-inverse-of
    lemma : Inverse.to finB F.∘ (⟶-finitary-fromVec finA finB vec) F.∘ Inverse.from finA ⟨$⟩_ ≗ flip lookup vec
    lemma i = begin _ ≡⟨ rinv₂ _ ⟩ _
                      ≡⟨ P.cong (flip lookup vec) (rinv₁ i)  ⟩ lookup i vec ∎
                      
⟶-finitary : ∀{m n a b p q}{A : Setoid a p}{B : Setoid b q} → Finitary A n → Finitary B m
                 → Finitary (A ⇨ B) (m ^ n)
⟶-finitary finA finB = exponent  Inv.∘ (⟶-finitary↔Vec finA finB)                 
