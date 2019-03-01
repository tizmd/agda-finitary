module Data.Fin.Subset.Properties.Cardinality where

open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Properties as NP
open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties 
open import Data.Vec using (_∷_; [])
open import Data.Vec.Any  using (here ; there)
open import Data.Vec.Properties as VP
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq 

-- some trivial lemma

∣p∣≡0→≡⊥  : ∀ {n}(p : Subset n) → ∣ p ∣ ≡ 0 → p ≡ ⊥
∣p∣≡0→≡⊥ {ℕ.zero} [] refl = refl
∣p∣≡0→≡⊥ {ℕ.suc n} (outside ∷ p) eq = cong (outside ∷_) (∣p∣≡0→≡⊥ p eq)
∣p∣≡0→≡⊥ {ℕ.suc n} (inside ∷ p) () 

∣p∣≡n→≡⊤  : ∀ {n}(p : Subset n) → ∣ p ∣ ≡ n → p ≡ ⊤
∣p∣≡n→≡⊤ {ℕ.zero} [] refl = refl
∣p∣≡n→≡⊤ {ℕ.suc n} (outside ∷ p) eq = ⊥-elim (1+n≰n (≤-respˡ-≈ eq (∣p∣≤n p)))
  where
    open IsPartialOrder NP.≤-isPartialOrder using (≤-respˡ-≈) 
∣p∣≡n→≡⊤ {ℕ.suc n} (inside ∷ p) eq = cong (inside ∷_) (∣p∣≡n→≡⊤ p (NP.suc-injective eq)) 

∣p∣≡1→≡⁅x⁆ : ∀ {n}(p : Subset n) → ∣ p ∣ ≡ 1 → ∃ λ x → p ≡ ⁅ x ⁆ 
∣p∣≡1→≡⁅x⁆ {ℕ.zero} [] ()
∣p∣≡1→≡⁅x⁆ {ℕ.suc n} (outside ∷ p) eq with ∣p∣≡1→≡⁅x⁆ p eq
... | x , q = suc x , cong (outside ∷_) q
∣p∣≡1→≡⁅x⁆ {ℕ.suc n} (inside ∷ p) eq rewrite ∣p∣≡0→≡⊥ p (NP.suc-injective eq) = zero , refl

-- union

≤∪ˡ : ∀ {n} {p} (q : Subset n) → ∣ p ∣ ℕ.≤  ∣ p ∪ q ∣     
≤∪ˡ {n}{p} q = p⊆q⇒∣p∣<∣q∣ (p⊆p∪q {p = p} q)
≤∪ʳ : ∀ {n} (p q : Subset n) → ∣ q ∣ ℕ.≤  ∣ p ∪ q ∣     
≤∪ʳ p q =  p⊆q⇒∣p∣<∣q∣ (q⊆p∪q p q)

∪≤ : ∀ {n} (p q : Subset n) → ∣ p ∪ q ∣ ℕ.≤ ∣ p ∣ ℕ.+ ∣ q ∣
∪≤ {ℕ.zero} [] [] = ℕ.z≤n
∪≤ {ℕ.suc n} (outside ∷ p) (outside ∷ q) = ∪≤ p q
∪≤ {ℕ.suc n} (outside ∷ p) (inside ∷ q) rewrite +-suc ∣ p ∣ ∣ q ∣ = ℕ.s≤s (∪≤ p q)
∪≤ {ℕ.suc n} (inside ∷ p) (outside ∷ q) = ℕ.s≤s (∪≤ p q)
∪≤ {ℕ.suc n} (inside ∷ p) (inside ∷ q) = ℕ.s≤s (NP.≤-trans (∪≤ p q) (NP.+-mono-≤ (≤-refl {∣ p ∣}) (n≤1+n _)))



disjoint-∪≡+ : ∀ {n} (p q : Subset n) → p ∩ q ≡ ⊥ → ∣ p ∪ q ∣ ≡ ∣ p ∣ ℕ.+ ∣ q ∣
disjoint-∪≡+ {ℕ.zero} [] [] refl = refl
disjoint-∪≡+ {ℕ.suc n} (outside ∷ p) (outside ∷ q) dis = disjoint-∪≡+ p q (VP.∷-injectiveʳ dis)
disjoint-∪≡+ {ℕ.suc n} (outside ∷ p) (inside ∷ q) dis =
  Eq.trans (Eq.cong ℕ.suc (disjoint-∪≡+ p q (VP.∷-injectiveʳ dis))) (Eq.sym (NP.+-suc _ _))
disjoint-∪≡+ {ℕ.suc n} (inside ∷ p) (outside ∷ q) dis = Eq.cong ℕ.suc (disjoint-∪≡+ p q (VP.∷-injectiveʳ dis))
disjoint-∪≡+ {ℕ.suc n} (inside ∷ p) (inside ∷ q) ()

module _ {n : ℕ} where
  open import Algebra.Structures {A = Subset n} _≡_
  open IsBooleanAlgebra (∪-∩-isBooleanAlgebra n) renaming (∧-complementʳ to ∩-complementʳ; ∨-complementʳ to ∪-complementʳ) 
  ∣p∣+∣∁p∣≡n : ∀ (p : Subset n) → ∣ p ∣  ℕ.+ ∣ ∁ p ∣ ≡ n
  ∣p∣+∣∁p∣≡n p = ∣ p ∣  ℕ.+ ∣ ∁ p ∣
                     ≡⟨ Eq.sym (disjoint-∪≡+ _ _ (∩-complementʳ p)) ⟩ _
                     ≡⟨ Eq.cong ∣_∣ (∪-complementʳ p) ⟩ _                     
                     ≡⟨ ∣⊤∣≡n _ ⟩ n ∎
    where
      open Eq.≡-Reasoning

∩≤ˡ : ∀ {n} (a b : Subset n) → ∣ a ∩ b ∣  ℕ.≤  ∣ a ∣
∩≤ˡ {n} a b = p⊆q⇒∣p∣<∣q∣ (p∩q⊆p a b)

∩≤ʳ : ∀ {n} (a b : Subset n) → ∣ a ∩ b ∣  ℕ.≤  ∣ b ∣
∩≤ʳ {n} a b = p⊆q⇒∣p∣<∣q∣ (p∩q⊆q a b)

{-
  module _ {n : ℕ} where
    open BooleanAlgebra (booleanAlgebra n) public using ()
      renaming (∨-complementʳ to ∪-complementʳ;
                ∧-complementʳ to ∩-complementʳ;
                ∨-∧-distribʳ   to ∪-∩-distribʳ
                )

    open import Algebra.Properties.BooleanAlgebra as BA
    open BA (booleanAlgebra n) public using ()
      renaming (∨-identityʳ to ∪-identityʳ;
                ∧-identityʳ to ∩-identityʳ;
                ∨-zeroʳ to ∪-zeroʳ;
                ∧-zeroʳ to ∩-zeroʳ;
                ∨-∧-commutativeSemiring to ∪-∩-commutativeSemiring
                )
                
    open CommutativeSemiring (∪-∩-commutativeSemiring) public renaming (distrib to ∪-∩-distrib) using ()
  -- complement
     
  size-complement : ∀ {n} (a : Subset n) → ∣ a ∣  ℕ.+ ∣ ∁ a ∣ ≡ n
  size-complement {n} a = begin ∣ a ∣  ℕ.+ ∣ ∁ a ∣ ≡⟨ sym (disjoint-∪≡ (∩-complementʳ a)) ⟩ ∣ a ∪ ∁ a ∣
                                                 ≡⟨ cong size (∪-complementʳ a) ⟩ ∣ ⊤{n} ∣
                                                 ≡⟨ ∣⊤∣{n} ⟩ n ∎ 
    where
      open P.≡-Reasoning
-}      
  -- intersection
{-  
  

private
  open import Relation.Nullary.Negation using (contraposition)
  p∩∁q≡⊥→p⊆q :  ∀ {n} {p q : Subset n} → p ∩ ∁ q ≡ ⊥ → p ⊆ q
  p∩∁q≡⊥→p⊆q {zero} {[]} {[]} refl ()
  p∩∁q≡⊥→p⊆q {suc n} {true ∷ p} {outside ∷ q} () here
  p∩∁q≡⊥→p⊆q {suc n} {inside ∷ p} {inside ∷ q} eq here = here
  p∩∁q≡⊥→p⊆q {suc n} {true ∷ p} {_ ∷ q} eq (there x∈p) with ∷-injective eq
  ... | _ , teq = there (p∩∁q≡⊥→p⊆q teq x∈p)
  p∩∁q≡⊥→p⊆q {suc n} {outside ∷ p} {_ ∷ q} eq (there x∈p) with ∷-injective eq
  ... | _ , teq = there (p∩∁q≡⊥→p⊆q teq x∈p)
  
  p∩q≡p→p⊆q : ∀ {n} {p q : Subset n} → p ∩ q ≡ p → p ⊆ q
  p∩q≡p→p⊆q {zero} {[]} {[]} refl ()
  p∩q≡p→p⊆q {suc n} {inside ∷ p} {x ∷ q} eq here with ∷-injective eq
  p∩q≡p→p⊆q {suc n} {inside ∷ p} {.inside ∷ q} eq here | refl , _ = here 
  p∩q≡p→p⊆q {suc n} {inside ∷ p} {_ ∷ q} eq (there x∈p) with ∷-injective eq
  ... | _ , teq = there (p∩q≡p→p⊆q teq x∈p)
  p∩q≡p→p⊆q {suc n} {outside ∷ p} {_ ∷ q} eq (there x∈p) with ∷-injective eq
  ... | _ , teq = there (p∩q≡p→p⊆q teq x∈p)    
  p⊈q→p∩q≢p : ∀ {n} {p q : Subset n} → p ⊈ q → p ∩ q ≢ p
  p⊈q→p∩q≢p = contraposition p∩q≡p→p⊆q

  split-size : ∀ {n} {a} (b : Subset n) → ∣ a ∣ ≡ ∣ a ∩ b ∣ ℕ.+ ∣ a ∩ ∁ b ∣
  split-size {n}{a} b = ∣a∣≡∣a∩b∣+∣a∩∁b∣
    where
      open P.≡-Reasoning 
      a∩b∩a∩∁b≡⊥ : (a ∩ b) ∩ (a ∩ ∁ b) ≡ ⊥   
      a∩b∩a∩∁b≡⊥ = begin
                   (a ∩ b) ∩ (a ∩ ∁ b) ≡⟨ ∩-assoc _ _ _ ⟩ _
                                       ≡⟨ cong (a ∩_ ) (sym (∩-assoc _ _ _)) ⟩ _
                                       ≡⟨ cong (a ∩_ ) (cong (_∩ _) (∩-comm _ _)) ⟩ _
                                       ≡⟨ cong (a ∩_ ) (∩-assoc _ _ _) ⟩ _
                                       ≡⟨ cong (a ∩_ ) (cong (a ∩_) (∩-complementʳ _)) ⟩ _
                                       ≡⟨ cong (a ∩_ ) (∩-zeroʳ _) ⟩ _
                                       ≡⟨ ∩-zeroʳ _ ⟩ ⊥
                   ∎
      a≡a∩b∪a∩∁b : a ≡ (a ∩ b) ∪ (a ∩ ∁ b)
      a≡a∩b∪a∩∁b = begin
                     a ≡⟨ sym (∩-identityʳ _) ⟩ a ∩ ⊤
                       ≡⟨ cong (_ ∩_) (sym (∪-complementʳ _)) ⟩ a ∩ (b ∪ ∁ b)
                       ≡⟨ (proj₁ ∪-∩-distrib) _ _ _  ⟩ (a ∩ b) ∪ (a ∩ ∁ b)
                   ∎
      ∣a∣≡∣a∩b∣+∣a∩∁b∣ : ∣ a ∣ ≡ ∣ a ∩ b ∣ ℕ.+ ∣ a ∩ ∁ b ∣
      ∣a∣≡∣a∩b∣+∣a∩∁b∣ = begin
                         ∣ a ∣ ≡⟨ cong size a≡a∩b∪a∩∁b ⟩ ∣ (a ∩ b) ∪ (a ∩ ∁ b) ∣
                              ≡⟨ disjoint-∪≡ a∩b∩a∩∁b≡⊥ ⟩  ∣ a ∩ b ∣ ℕ.+ ∣ a ∩ ∁ b ∣
                      ∎

  ⊈→∩<ˡ : ∀ {n} {a b : Subset n} → a ⊈ b → ∣ a ∩ b ∣ ℕ.< ∣ a ∣  
  ⊈→∩<ˡ {n}{a}{b} a⊈b = ≤+≢⇒< (∩≤ˡ a b) lemma
    where
      open P.≡-Reasoning 

      n+m≡n→m≡0 : ∀ {n m} → n ℕ.+ m ≡ n → m ≡ 0
      n+m≡n→m≡0 {n}{m} eq = +-cancelˡ-≡ n (P.trans eq (sym (+-identityʳ n)))
      
      lemma : ∣ a ∩ b ∣ ≢ ∣ a ∣  
      lemma eq = (contraposition p∩∁q≡⊥→p⊆q a⊈b) (size0 (n+m≡n→m≡0 (sym (P.trans eq (split-size b)))))
-}  
