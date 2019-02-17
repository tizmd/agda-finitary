module Data.Fin.Subset.Cardinality where
  open import Data.Fin
  open import Data.Nat as ℕ
  open import Data.Nat.Properties 
  open import Data.Fin.Subset
  open import Data.Fin.Subset.Properties using (⊆⊤; p⊆p∪q; q⊆p∪q ; p∩q⊆p ; p∩q⊆q; ∩-assoc; ∩-comm; ∪-assoc; ∪-comm)
  open import Data.Vec as Vec hiding (_∈_)
  open import Data.Vec.Properties using (∷-injective)
  open import Relation.Nullary
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; cong; refl; sym)
  open import Data.Bool as B
  open import Data.Product
  open import Data.Empty using (⊥-elim)
  open import Function
  open import Algebra  

  _∖_ : ∀ {n} → Subset n → Subset n → Subset n
  _∖_ {n} a b = a ∩ ∁ b

  -- some trivial lemma
  ∣⊥∣ :  ∀ {n} → ∣ ⊥{n} ∣ ≡ 0
  ∣⊥∣ {zero} = refl
  ∣⊥∣ {suc n} = ∣⊥∣ {n}

  size0 : ∀ {n} {a : Subset n} → ∣ a ∣ ≡ 0 → a ≡ ⊥
  size0 {zero} {[]} refl = refl
  size0 {suc n} {true ∷ a} ()
  size0 {suc n} {outside ∷ a} eq = cong (outside ∷_) (size0 eq)
  
  ∣⊤∣ : ∀ {n} → ∣ ⊤{n} ∣ ≡ n
  ∣⊤∣ {zero} = refl
  ∣⊤∣ {suc n} = cong suc (∣⊤∣ {n})

  |⁅_⁆| : ∀ {n} (i : Fin n) → ∣ ⁅ i ⁆ ∣ ≡ 1
  |⁅_⁆| {zero} ()
  |⁅_⁆| {suc n} zero = cong ℕ.suc (∣⊥∣ {n})
  |⁅_⁆| {suc n} (suc i) = |⁅ i ⁆|

  -- ⊆

  private
    tail-⊆ : ∀ {n} {x y : Side}{a b : Subset n} → x ∷ a ⊆ y ∷ b → a ⊆ b
    tail-⊆ f {z} z∈a with f (there z∈a)
    tail-⊆ f {x} z∈a | there z∈b = z∈b
  size-⊆ : ∀ {n} {a b : Subset n} → a ⊆ b → ∣ a ∣ ℕ.≤ ∣ b ∣
  size-⊆ {zero} {[]} {[]} a⊆b = z≤n
  size-⊆ {suc n} {s ∷ a} {s₁ ∷ b} a⊆b with s B.≟ inside
  size-⊆ {suc n} {.inside ∷ a} {s₁ ∷ b} a⊆b | yes refl with a⊆b here
  size-⊆ {suc n} {.inside ∷ a} {.inside ∷ b} a⊆b | yes refl | here = s≤s (size-⊆ (tail-⊆ a⊆b))
  size-⊆ {suc n} {inside ∷ a} {s₁ ∷ b} a⊆b | no s≢inside = ⊥-elim (s≢inside refl)
  size-⊆ {suc n} {outside ∷ a} {outside ∷ b} a⊆b | no s≢inside = size-⊆ (tail-⊆ a⊆b)
  size-⊆ {suc n} {outside ∷ a} {true ∷ b} a⊆b | no s≢inside = ≤-step (size-⊆ (tail-⊆ a⊆b))

  ∣_∣≤n : ∀ {n} (a : Subset n) → ∣ a ∣ ℕ.≤ n
  ∣_∣≤n {n} a with ∣⊤∣{n} | size-⊆ (⊆⊤ {p = a})
  ... | p | q rewrite p = q
  
  -- union

  ≤∪ˡ : ∀ {n} {a} (b : Subset n) → ∣ a ∣ ℕ.≤  ∣ a ∪ b ∣     
  ≤∪ˡ {n}{a} b = size-⊆ (p⊆p∪q b)

  ≤∪ʳ : ∀ {n} (a b : Subset n) → ∣ b ∣ ℕ.≤  ∣ a ∪ b ∣     
  ≤∪ʳ {n} a b = size-⊆ (q⊆p∪q a b)

  ∪≤ : ∀ {n} (a b : Subset n) → ∣ a ∪ b ∣ ℕ.≤ ∣ a ∣ ℕ.+ ∣ b ∣
  ∪≤ {zero} [] [] = z≤n
  ∪≤ {suc n} (outside ∷ a) (outside ∷ b) = ∪≤ a b
  ∪≤ {suc n} (outside ∷ a) (inside ∷ b) rewrite +-suc ∣ a ∣ ∣ b ∣ = s≤s (∪≤ a b)
  ∪≤ {suc n} (inside ∷ a) (outside ∷ b) = s≤s (∪≤ a b)
  ∪≤ {suc n} (inside ∷ a) (inside ∷ b) = s≤s (≤-trans (∪≤ a b) (lemma ∣ a ∣ ∣ b ∣))
    where
      lemma : ∀ n m → n ℕ.+ m ℕ.≤ n ℕ.+ suc m
      lemma n m = +-mono-≤ (≤-refl {n}) (n≤1+n m)


  disjoint-∪≡ : ∀ {n} {a b : Subset n} → a ∩ b ≡ ⊥ → ∣ a ∪ b ∣ ≡ ∣ a ∣ ℕ.+ ∣ b ∣
  disjoint-∪≡ = ?

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
      
  -- intersection

  ∩≤ˡ : ∀ {n} (a b : Subset n) → ∣ a ∩ b ∣  ℕ.≤  ∣ a ∣
  ∩≤ˡ {n} a b = size-⊆ (p∩q⊆p a b)

  ∩≤ʳ : ∀ {n} (a b : Subset n) → ∣ a ∩ b ∣  ℕ.≤  ∣ b ∣
  ∩≤ʳ {n} a b = size-⊆ (p∩q⊆q a b)
  
  
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

