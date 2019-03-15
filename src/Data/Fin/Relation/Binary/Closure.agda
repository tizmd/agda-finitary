{-# OPTIONS --safe --without-K #-}
module Data.Fin.Relation.Binary.Closure where

open import Data.Fin 
open import Data.Fin.Subset 
open import Data.Fin.Subset.Dec
open import Data.Fin.Subset.Properties
open import Data.Fin.Subset.Properties.Dec
open import Data.Nat as ℕ using (ℕ)
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary renaming (Decidable to Dec₂) 
open import Function using (flip; _∘_; case_of_; _∋_)
open import Data.List as List using (List; _∷_; [])
open import Data.Sum
import Data.List.Membership.Propositional as Mem
open import Data.List.Membership.Propositional.Properties as MemP
open import Data.Product
open import Induction.Nat
open import Data.Vec using (Vec; []; _∷_; here)
open import Data.Vec.Properties
open import Data.Bool.Properties as B
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Nat.Properties as ℕP
open import Function.Equivalence using (Equivalence)
open import Function.Equality using (_⟨$⟩_)

private
  iter : ∀ {a}{A : Set a} → (A → A) → A → ℕ → A
  iter f z ℕ.zero = z
  iter f z (ℕ.suc n) = f (iter f z n)
  _≟s_ : ∀ {n} → Dec₂ (_≡_{A = Subset n})
  _≟s_ = ≡-dec B._≟_
  p⊂q⇒∣p∣<∣q∣ : ∀ {n} {p q : Subset n} → p ⊆ q → p ≢ q → ∣ p ∣ ℕ.< ∣ q ∣
  p⊂q⇒∣p∣<∣q∣ {p = []} {[]} p⊆q p≢q = contradiction refl p≢q
  p⊂q⇒∣p∣<∣q∣ {p = outside ∷ p} {outside ∷ q} p⊆q p≢q = p⊂q⇒∣p∣<∣q∣ (drop-∷-⊆ p⊆q) (p≢q ∘ cong (outside ∷_))
  p⊂q⇒∣p∣<∣q∣ {p = outside ∷ p} {inside ∷ q} p⊆q p≢q = ℕ.s≤s (p⊆q⇒∣p∣<∣q∣ (drop-∷-⊆ p⊆q))
  p⊂q⇒∣p∣<∣q∣ {p = inside ∷ p} {outside ∷ q} p⊆q p≢q = contradiction (p⊆q here) λ ()
  p⊂q⇒∣p∣<∣q∣ {p = inside ∷ p} {inside ∷ q} p⊆q p≢q = ℕ.s≤s (p⊂q⇒∣p∣<∣q∣ (drop-∷-⊆ p⊆q) (p≢q ∘ cong (inside ∷_)))

  m<n⇒0<n : ∀ {m n} → m ℕ.< n → 0 ℕ.< n
  m<n⇒0<n (ℕ.s≤s m<n) = ℕ.s≤s ℕ.z≤n
  
  saturate : ∀ {n} → (f : Subset n → Subset n) → (∀ {s} → s ⊆ f s) → (z : Subset n) → iter f z n ≡ iter f z (ℕ.suc n)
  saturate {n} f p z = case rec P g n of
          λ { (inj₁ eq) → eq ;
               (inj₂ n<f) → contradiction n<f (≤⇒≯ (∣p∣≤n (f (iter f z n)))) }
    where
      open ℕP.≤-Reasoning 
      P : ℕ → Set 
      P n = iter f z n ≡ iter f z (ℕ.suc n) ⊎ n ℕ.< ∣ iter f z (ℕ.suc n) ∣

      g : ∀ n → Rec _ P n → P n
      g ℕ.zero _ with z ≟s f z
      ... | yes eq = inj₁ eq
      ... | no  z≢fz = inj₂ (m<n⇒0<n (p⊂q⇒∣p∣<∣q∣ p z≢fz))
      g (ℕ.suc n) (inj₁ eq) = inj₁ (cong f eq)
      g (ℕ.suc n) (inj₂ n<f) with f (iter f z n) ≟s f (iter f z (ℕ.suc n))
      ... | yes eq = inj₁ eq
      ... | no  neq = inj₂ (begin-strict ℕ.suc n <⟨ ℕ.s≤s n<f ⟩ _ ≤⟨ p⊂q⇒∣p∣<∣q∣ p neq ⟩ _ ∎)
      
  ∈-saturate : ∀ {n}(f : Subset n → Subset n)(p : ∀ {s} → s ⊆ f s) z {i} → (∃ λ m → i ∈ iter f z m) → i ∈ iter f z n
  ∈-saturate {n} f p z (m , i∈fm) with n ℕP.≤? m

  ... | yes n≤m rewrite sym (ℕP.m∸n+n≡m n≤m) = subst (_ ∈_) (sym (lemma (m ℕ.∸ n))) i∈fm 
    where
      lemma : ∀ k → iter f z n ≡ iter f z (k ℕ.+ n)
      lemma 0 = refl
      lemma (ℕ.suc k) = trans (saturate f p z) (cong f (lemma k))
      
  ... | no n≰m  rewrite sym (ℕP.m∸n+n≡m (ℕP.≰⇒> n≰m)) = lemma (n ℕ.∸ ℕ.suc m) (p i∈fm)  
    where
      lemma : ∀ k {m j} → j ∈ iter f z m → j ∈ iter f z (k ℕ.+ m)
      lemma 0 j∈fm = j∈fm
      lemma (ℕ.suc k) j∈fm = p (lemma k j∈fm) 
      
  
module _ {n} where 

  open import Data.List.Relation.Unary.Any

  ∈-⋃⁺ : ∀{s}{ss : List (Subset n)} → s Mem.∈ ss → ∀ {i} → i ∈ s → i ∈ ⋃ ss
  ∈-⋃⁺ {ss = []} () i∈s
  ∈-⋃⁺ {ss = s ∷ ss} (here refl) i∈s = x∈p∪q⁺ (inj₁ i∈s)
  ∈-⋃⁺ {ss = _ ∷ ss} (there s∈ss) i∈s = x∈p∪q⁺ (inj₂ (∈-⋃⁺ s∈ss i∈s))

  ∈-⋃⁻ : ∀{ss : List (Subset n)}{i} → i ∈ ⋃ ss → ∃ λ s → i ∈ s × s Mem.∈ ss 
  ∈-⋃⁻ {[]} i∈ss = contradiction i∈ss ∉⊥ 
  ∈-⋃⁻ {s ∷ ss} i∈ss with x∈p∪q⁻ _ _ i∈ss
  ∈-⋃⁻ {s ∷ ss} i∈ss | inj₁ i∈s = s , i∈s , here refl 
  ∈-⋃⁻ {_ ∷ ss} i∈ss | inj₂ i∈rest with ∈-⋃⁻ {ss} i∈rest
  ... | s , i∈s , s∈ss = s , i∈s , there s∈ss
  
  
module _ {p n}{P : Rel (Fin n) p} where
  right-image : Dec₂ P → Fin n → Subset n 
  right-image P? i = subset (P? i)

  left-image  : Dec₂ P → Fin n → Subset n 
  left-image P? i = subset (flip P? i)


  _◃_ : Subset n → Dec₂ P → Subset n
  s ◃ P? = ⋃ (List.map (right-image P?) (List.filter (_∈? s) (List.allFin _)))

  _▹_ :  Dec₂ P → Subset n → Subset n
  P? ▹ s = ⋃ (List.map (left-image P?) (List.filter (_∈? s) (List.allFin _)))

  _∪▹_ : Dec₂ P → Subset n →  Subset n
  P? ∪▹ s = s ∪ (P? ▹ s)

  ∪▹-monotone : (P? : Dec₂ P) → ∀ {s} → s ⊆ P? ∪▹ s
  ∪▹-monotone P? {s} = p⊆p∪q (P? ▹ s)

  ∈-▹⁺ : ∀ {i s j}(P? : Dec₂ P) → j ∈ s → P i j → i ∈ P? ▹ s
  ∈-▹⁺ {i}{s}{j} P? i∈s pij = ∈-⋃⁺ (∈-map⁺ (left-image P?) (∈-filter⁺ (_∈? s) (∈-allFin _) i∈s))  (∈subset⁺ (flip P? j) pij)
  
  ∈-▹⁻ : ∀ {i s}(P? : Dec₂ P) → i ∈ P? ▹ s → ∃ λ j → j ∈ s × P i j 
  ∈-▹⁻ {i}{s} P? i∈s with ∈-⋃⁻ {ss = List.map (left-image P?) (List.filter (_∈? s) (List.allFin _))} i∈s
  ... | P▹s , i∈P▹s , P▹s∈ss with ∈-map⁻ _ P▹s∈ss
  ... | j , j∈l , eq rewrite eq with ∈-filter⁻  (_∈? s) {xs = List.allFin _} j∈l
  ... | _ , j∈s         = j ,  j∈s , ∈subset⁻ (flip P? j) i∈P▹s
  
  iter-∪▹ : Subset n → (P? : Dec₂ P) → ℕ → Subset n
  iter-∪▹ z P? = iter (P? ∪▹_) z


  ▹-star : (P? : Dec₂ P) → Fin n → ℕ → Subset n
  ▹-star P? i = iter-∪▹ ⁅ i ⁆ P? 

  ▹-plus : (P? : Dec₂ P) → Fin n → ℕ → Subset n
  ▹-plus P? j = iter-∪▹ (left-image P? j) P?
  
  ∈-▹-star⁺ : (P? : Dec₂ P) → ∀ {i j} → Star P i j → i ∈ ▹-star P? j n
  ∈-▹-star⁺ P? {i}{j} pij = ∈-saturate _ (∪▹-monotone P?) ⁅ j ⁆ (rec Q g (length pij) pij refl)
    where
       length : ∀ {i j} → Star P i j → ℕ
       length ε = 0
       length (_ ◅ r) = 1 ℕ.+ length r
       
       Q : ℕ → Set _
       Q m = ∀ {i j} → (r : Star P i j) → length r ≡ m → ∃ λ k → i ∈ ▹-star P? j k

       g : ∀ m → Rec _ Q m → Q m
       g .0 ih ε refl = 0 , x∈⁅x⁆ _
       g .(ℕ.suc (length rkj)) ih (pik ◅ rkj) refl with ih rkj refl
       ... | k , i∈fk = 1 ℕ.+ k , x∈p∪q⁺ (inj₂ (∈-▹⁺ P? i∈fk pik))

    
  ∈-▹-star⁻ : (P? : Dec₂ P) → ∀ {i j} m → i ∈ ▹-star P? j m → Star P i j
  ∈-▹-star⁻ P? {i} {j} ℕ.zero h rewrite x∈⁅y⁆⇒x≡y _ h = ε
  ∈-▹-star⁻ P? {i} {j} (ℕ.suc m) h with x∈p∪q⁻ _ _ h
  ... | inj₁ h₁ = ∈-▹-star⁻ P? m h₁ 
  ... | inj₂ h₁  with ∈-▹⁻ P? h₁
  ... | k , k∈s , pik = pik ◅ ∈-▹-star⁻ P? m k∈s
  
  ∈-▹-plus⁺ : (P? : Dec₂ P) → ∀ {i j} → Plus′ P i j → i ∈ ▹-plus P? j n
  ∈-▹-plus⁺ P? {i}{j} pij = ∈-saturate _ (∪▹-monotone P?) (left-image P? j) (rec Q g (length pij) pij refl)
     where
       length : ∀ {i j} → Plus′ P i j → ℕ
       length [ x∼y ] = 0
       length (x∼y ∷ r) = 1 ℕ.+ length r
       
       Q : ℕ → Set _
       Q m = ∀ {i j} → (r : Plus′ P i j) → length r ≡ m → ∃ λ k → i ∈ ▹-plus P? j k

       g : ∀ m → Rec _ Q m → Q m
       g ℕ.zero ih {i}{j} [ pij ] refl = 0 , ∈subset⁺ (flip P? j) pij 
       g (ℕ.suc .(length r)) ih {i}{j} (pik ∷ r) refl with ih r refl
       ... | k , i∈fk = 1 ℕ.+ k , x∈p∪q⁺ (inj₂ (∈-▹⁺ P? i∈fk pik))

  ∈-▹-plus⁻ : (P? : Dec₂ P) → ∀ {i j} m → i ∈ ▹-plus P? j m → Plus′ P i j
  ∈-▹-plus⁻ P? {i} {j} ℕ.zero h = [ ∈subset⁻ (flip P? j) h ]
  ∈-▹-plus⁻ P? {i} {j} (ℕ.suc m) h with x∈p∪q⁻ _ _ h
  ∈-▹-plus⁻ P? {i} {j} (ℕ.suc m) h | inj₁ h₁  = ∈-▹-plus⁻ P? m h₁
  ∈-▹-plus⁻ P? {i} {j} (ℕ.suc m) h | inj₂ h₁  with ∈-▹⁻ P? h₁
  ... | k , k∈s , pik = pik ∷ ∈-▹-plus⁻ P? m k∈s 


  -- Derived decidability of closures 

  dec-Star : (P? : Dec₂ P) → Dec₂ (Star P)
  dec-Star P? i j with i ∈? ▹-star P? j n
  ... | yes i∈star = yes (∈-▹-star⁻ P? n i∈star)
  ... | no i∉star  = no λ h → contradiction (∈-▹-star⁺ P? h) i∉star
  
  dec-Plus′ : (P? : Dec₂ P) → Dec₂ (Plus′ P)
  dec-Plus′ P? i j with i ∈? ▹-plus P? j n
  ... | yes i∈plus = yes (∈-▹-plus⁻ P? n i∈plus)
  ... | no i∉plus  = no λ h → contradiction (∈-▹-plus⁺ P? h) i∉plus

  dec-Plus : (P? : Dec₂ P) → Dec₂ (Plus P)
  dec-Plus P? i j with dec-Plus′ P? i j
  ... | yes pij′ = yes (Equivalence.from equivalent ⟨$⟩ pij′)
  ... | no ¬pij′ = no λ pij → ¬pij′ (Equivalence.to equivalent ⟨$⟩ pij)
