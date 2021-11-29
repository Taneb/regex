{-# OPTIONS --safe --without-K #-}

open import Relation.Binary

module Regex.Properties {c ℓ} (Alphabet : DecSetoid c ℓ) where

open DecSetoid Alphabet using () renaming (Carrier to A)
open import Regex Alphabet

open import Algebra.Bundles
import Algebra.Definitions
import Algebra.Structures
import Algebra.Solver.CommutativeMonoid as CMSolver
import Algebra.Solver.IdempotentCommutativeMonoid as ICMSolver
open import Data.Empty
open import Data.Fin.Base using (zero; suc)
open import Data.List
open import Data.Product
open import Data.Vec.Base using (_∷_; [])
open import Function.Base
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- forall xs, ⟨ xs ⟩_≈_ is an equalivalence relation

⟨_⟩≈RL-refl : ∀ xs → Reflexive (⟨ xs ⟩_≈RL_)
⟨ xs ⟩≈RL-refl = id , id

⟨_⟩≈RL-sym : ∀ xs → Symmetric ⟨ xs ⟩_≈RL_
⟨ xs ⟩≈RL-sym p = swap p

⟨_⟩≈RL-trans : ∀ xs → Transitive ⟨ xs ⟩_≈RL_
⟨ xs ⟩≈RL-trans p q = Data.Product.zip (flip _∘′_) _∘′_ p q

⟨_⟩≈RL-isEquivalence : ∀ xs → IsEquivalence ⟨ xs ⟩_≈RL_
⟨ xs ⟩≈RL-isEquivalence = record
  { refl  = ⟨ xs ⟩≈RL-refl
  ; sym   = ⟨ xs ⟩≈RL-sym
  ; trans = ⟨ xs ⟩≈RL-trans
  }

⟨_⟩RL-setoid : (xs : List A) → Setoid c c
⟨ xs ⟩RL-setoid = record { isEquivalence = ⟨ xs ⟩≈RL-isEquivalence }

-- _≈RL_ is an equivalence relation
≈RL-refl : Reflexive _≈RL_
≈RL-refl xs = ⟨ xs ⟩≈RL-refl

≈RL-sym : Symmetric _≈RL_
≈RL-sym p xs = ⟨ xs ⟩≈RL-sym (p xs)

≈RL-trans : Transitive _≈RL_
≈RL-trans p q xs = ⟨ xs ⟩≈RL-trans (p xs) (q xs)

≈RL-isEquivalence : IsEquivalence _≈RL_
≈RL-isEquivalence = record
  { refl = ≈RL-refl
  ; sym = ≈RL-sym
  ; trans = ≈RL-trans
  }

RL-setoid : Setoid c c
RL-setoid = record { isEquivalence = ≈RL-isEquivalence }

-- Algebraic properties of regular languages

module _ where
  open Algebra.Definitions
  open Algebra.Structures

  ⟨_⟩-∪-cong : ∀ xs → Congruent₂ ⟨ xs ⟩_≈RL_ _∪_
  ⟨ [] ⟩-∪-cong {x} {y} {u} {v} x≈y u≈v = lemma₁ , lemma₂
    where
      lemma₁ : Accepts (x ∪ u) [] → Accepts (y ∪ v) []
      lemma₁ (∪Acceptsεˡ .x .u p) = ∪Acceptsεˡ y v (proj₁ x≈y p)
      lemma₁ (∪Acceptsεʳ .x .u p) = ∪Acceptsεʳ y v (proj₁ u≈v p)
  
      lemma₂ : Accepts (y ∪ v) [] → Accepts (x ∪ u) []
      lemma₂ (∪Acceptsεˡ .y .v p) = ∪Acceptsεˡ x u (proj₂ x≈y p)
      lemma₂ (∪Acceptsεʳ .y .v p) = ∪Acceptsεʳ x u (proj₂ u≈v p)
  ⟨ a ∷ as ⟩-∪-cong {x} {y} {u} {v} x≈y u≈v = ⟨ as ⟩-∪-cong x≈y u≈v

  ⟨_⟩-∪-assoc : ∀ xs → Associative ⟨ xs ⟩_≈RL_ _∪_
  ⟨ [] ⟩-∪-assoc r s t = lemma₁ , lemma₂
      where
      lemma₁ : Accepts ((r ∪ s) ∪ t) [] → Accepts (r ∪ (s ∪ t)) []
      lemma₁ (∪Acceptsεˡ .(r ∪ s) .t (∪Acceptsεˡ .r .s p)) = ∪Acceptsεˡ r (s ∪ t) p
      lemma₁ (∪Acceptsεˡ .(r ∪ s) .t (∪Acceptsεʳ .r .s p)) = ∪Acceptsεʳ r (s ∪ t) (∪Acceptsεˡ s t p)
      lemma₁ (∪Acceptsεʳ .(r ∪ s) .t p) = ∪Acceptsεʳ r (s ∪ t) (∪Acceptsεʳ s t p)

      lemma₂ : Accepts (r ∪ (s ∪ t)) [] → Accepts ((r ∪ s) ∪ t) []
      lemma₂ (∪Acceptsεˡ .r .(s ∪ t) p) = ∪Acceptsεˡ (r ∪ s) t (∪Acceptsεˡ r s p)
      lemma₂ (∪Acceptsεʳ .r .(s ∪ t) (∪Acceptsεˡ .s .t p)) = ∪Acceptsεˡ (r ∪ s) t (∪Acceptsεʳ r s p)
      lemma₂ (∪Acceptsεʳ .r .(s ∪ t) (∪Acceptsεʳ .s .t p)) = ∪Acceptsεʳ (r ∪ s) t p
  ⟨ x ∷ xs ⟩-∪-assoc r s t = ⟨ xs ⟩-∪-assoc (δ x r) (δ x s) (δ x t)

  ⟨_⟩-∪-comm : ∀ xs → Commutative ⟨ xs ⟩_≈RL_ _∪_
  ⟨ [] ⟩-∪-comm r s = lemma₁ , lemma₂
    where
      lemma₁ : Accepts (r ∪ s) [] → Accepts (s ∪ r) []
      lemma₁ (∪Acceptsεˡ .r .s x) = ∪Acceptsεʳ s r x
      lemma₁ (∪Acceptsεʳ .r .s x) = ∪Acceptsεˡ s r x

      lemma₂ : Accepts (s ∪ r) [] → Accepts (r ∪ s) []
      lemma₂ (∪Acceptsεˡ .s .r x) = ∪Acceptsεʳ r s x
      lemma₂ (∪Acceptsεʳ .s .r x) = ∪Acceptsεˡ r s x
  ⟨ x ∷ xs ⟩-∪-comm r s = ⟨ xs ⟩-∪-comm (δ x r) (δ x s)

  ⟨_⟩-∪-identityˡ : ∀ xs → LeftIdentity ⟨ xs ⟩_≈RL_ ∅ _∪_
  ⟨ [] ⟩-∪-identityˡ r = lemma₁ , lemma₂
    where
      lemma₁ : Accepts (∅ ∪ r) [] → Accepts r []
      lemma₁ (∪Acceptsεʳ .∅ .r p) = p

      lemma₂ : Accepts r [] → Accepts (∅ ∪ r) []
      lemma₂ p = ∪Acceptsεʳ ∅ r p
  ⟨ x ∷ xs ⟩-∪-identityˡ r = ⟨ xs ⟩-∪-identityˡ (δ x r)

  ⟨_⟩-∪-identityʳ : ∀ xs → RightIdentity ⟨ xs ⟩_≈RL_ ∅ _∪_
  ⟨ [] ⟩-∪-identityʳ r = lemma₁ , lemma₂
    where
      lemma₁ : Accepts (r ∪ ∅) [] → Accepts r []
      lemma₁ (∪Acceptsεˡ .r .∅ p) = p

      lemma₂ : Accepts r [] → Accepts (r ∪ ∅) []
      lemma₂ p = ∪Acceptsεˡ r ∅ p
  ⟨ x ∷ xs ⟩-∪-identityʳ r = ⟨ xs ⟩-∪-identityʳ (δ x r)

  ⟨_⟩-∪-idem : ∀ xs → Idempotent ⟨ xs ⟩_≈RL_ _∪_
  ⟨ [] ⟩-∪-idem r = lemma₁ , lemma₂
    where
      lemma₁ : Accepts (r ∪ r) [] → Accepts r []
      lemma₁ (∪Acceptsεˡ .r .r p) = p
      lemma₁ (∪Acceptsεʳ .r .r p) = p

      lemma₂ : Accepts r [] → Accepts (r ∪ r) []
      lemma₂ p = ∪Acceptsεˡ r r p
  ⟨ x ∷ xs ⟩-∪-idem r = ⟨ xs ⟩-∪-idem (δ x r)

  ⟨_⟩-∪-isMagma : ∀ xs → IsMagma ⟨ xs ⟩_≈RL_ _∪_
  ⟨ xs ⟩-∪-isMagma = record
    { isEquivalence = ⟨ xs ⟩≈RL-isEquivalence
    ; ∙-cong = ⟨ xs ⟩-∪-cong
    }

  ⟨_⟩-∪-isSemigroup : ∀ xs → IsSemigroup ⟨ xs ⟩_≈RL_ _∪_
  ⟨ xs ⟩-∪-isSemigroup = record
    { isMagma = ⟨ xs ⟩-∪-isMagma
    ; assoc = ⟨ xs ⟩-∪-assoc
    }

  ⟨_⟩-∪-isBand : ∀ xs → IsBand ⟨ xs ⟩_≈RL_ _∪_
  ⟨ xs ⟩-∪-isBand = record
    { isSemigroup = ⟨ xs ⟩-∪-isSemigroup
    ; idem = ⟨ xs ⟩-∪-idem
    }

  ⟨_⟩-∪-isCommutativeSemigroup : ∀ xs → IsCommutativeSemigroup ⟨ xs ⟩_≈RL_ _∪_
  ⟨ xs ⟩-∪-isCommutativeSemigroup = record
    { isSemigroup = ⟨ xs ⟩-∪-isSemigroup
    ; comm = ⟨ xs ⟩-∪-comm
    }

  ⟨_⟩-∪-isMonoid : ∀ xs → IsMonoid ⟨ xs ⟩_≈RL_ _∪_ ∅
  ⟨ xs ⟩-∪-isMonoid = record
    { isSemigroup = ⟨ xs ⟩-∪-isSemigroup
    ; identity = ⟨ xs ⟩-∪-identityˡ , ⟨ xs ⟩-∪-identityʳ
    }

  ⟨_⟩-∪-isCommutativeMonoid : ∀ xs → IsCommutativeMonoid ⟨ xs ⟩_≈RL_ _∪_ ∅
  ⟨ xs ⟩-∪-isCommutativeMonoid = record
    { isMonoid = ⟨ xs ⟩-∪-isMonoid
    ; comm = ⟨ xs ⟩-∪-comm
    }

  ⟨_⟩-∪-isIdempotentCommutativeMonoid : ∀ xs → IsIdempotentCommutativeMonoid ⟨ xs ⟩_≈RL_ _∪_ ∅
  ⟨ xs ⟩-∪-isIdempotentCommutativeMonoid = record
    { isCommutativeMonoid = ⟨ xs ⟩-∪-isCommutativeMonoid
    ; idem = ⟨ xs ⟩-∪-idem
    }


  ⟨_⟩-∪-commutativeMonoid : (xs : List A) → CommutativeMonoid c c
  ⟨ xs ⟩-∪-commutativeMonoid = record
    { isCommutativeMonoid = ⟨ xs ⟩-∪-isCommutativeMonoid
    }

  ⟨_⟩-∪-idempotentCommutativeMonoid : (xs : List A) → IdempotentCommutativeMonoid c c
  ⟨ xs ⟩-∪-idempotentCommutativeMonoid = record
    { isIdempotentCommutativeMonoid = ⟨ xs ⟩-∪-isIdempotentCommutativeMonoid
    }

  ⟨_⟩-；-distribˡ-∪ : ∀ xs → _DistributesOverˡ_ ⟨ xs ⟩_≈RL_ _；_ _∪_
  ⟨ [] ⟩-；-distribˡ-∪ r s t = lemma₁ , lemma₂
    where
      lemma₁ : Accepts (r ； (s ∪ t)) [] → Accepts ((r ； s) ∪ (r ； t)) []
      lemma₁ (；Acceptsε .r .(s ∪ t) p₁ (∪Acceptsεˡ .s .t p₂)) = ∪Acceptsεˡ (r ； s) (r ； t) (；Acceptsε r s p₁ p₂)
      lemma₁ (；Acceptsε .r .(s ∪ t) p₁ (∪Acceptsεʳ .s .t p₂)) = ∪Acceptsεʳ (r ； s) (r ； t) (；Acceptsε r t p₁ p₂)

      lemma₂ : Accepts ((r ； s) ∪ (r ； t)) [] → Accepts (r ； (s ∪ t)) []
      lemma₂ (∪Acceptsεˡ .(r ； s) .(r ； t) (；Acceptsε .r .s p₁ p₂)) = ；Acceptsε r (s ∪ t) p₁ (∪Acceptsεˡ s t p₂)
      lemma₂ (∪Acceptsεʳ .(r ； s) .(r ； t) (；Acceptsε .r .t p₁ p₂)) = ；Acceptsε r (s ∪ t) p₁ (∪Acceptsεʳ s t p₂)
  ⟨ x ∷ xs ⟩-；-distribˡ-∪ r s t with acceptsε? r
  ... | yes p = begin
    ((δ x s ∪ δ x t) ∪ (δ x r ； (s ∪ t))) ≈⟨ ⟨ xs ⟩-∪-cong ⟨ xs ⟩≈RL-refl (⟨ xs ⟩-；-distribˡ-∪ (δ x r) s t) ⟩
    ((δ x s ∪ δ x t) ∪ ((δ x r ； s) ∪ (δ x r ； t))) ≈⟨ prove 4 ((v₁ ⊕ v₂) ⊕ (v₃ ⊕ v₄)) ((v₁ ⊕ v₃) ⊕ (v₂ ⊕ v₄)) (δ x s ∷ δ x t ∷ (δ x r ； s) ∷ (δ x r ； t) ∷ []) ⟩
    ((δ x s ∪ (δ x r ； s)) ∪ (δ x t ∪ (δ x r ； t))) ∎
    where
      open SetoidReasoning ⟨ xs ⟩RL-setoid
      open CMSolver ⟨ xs ⟩-∪-commutativeMonoid
      v₁ = var zero
      v₂ = var (suc zero)
      v₃ = var (suc (suc zero))
      v₄ = var (suc (suc (suc zero)))
  ... | no ¬p = ⟨ xs ⟩-；-distribˡ-∪ (δ x r) s t

  ⟨_⟩-；-distribʳ-∪ : ∀ xs → _DistributesOverʳ_ ⟨ xs ⟩_≈RL_ _；_ _∪_
  ⟨ [] ⟩-；-distribʳ-∪ r s t = lemma₁ , lemma₂
    where
      lemma₁ : Accepts ((s ∪ t) ； r) [] → Accepts ((s ； r) ∪ (t ； r)) []
      lemma₁ (；Acceptsε .(s ∪ t) .r (∪Acceptsεˡ .s .t p₁) p₂) = ∪Acceptsεˡ (s ； r) (t ； r) (；Acceptsε s r p₁ p₂)
      lemma₁ (；Acceptsε .(s ∪ t) .r (∪Acceptsεʳ .s .t p₁) p₂) = ∪Acceptsεʳ (s ； r) (t ； r) (；Acceptsε t r p₁ p₂)

      lemma₂ : Accepts ((s ； r) ∪ (t ； r)) [] → Accepts ((s ∪ t) ； r) []
      lemma₂ (∪Acceptsεˡ .(s ； r) .(t ； r) (；Acceptsε .s .r p₁ p₂)) = ；Acceptsε (s ∪ t) r (∪Acceptsεˡ s t p₁) p₂
      lemma₂ (∪Acceptsεʳ .(s ； r) .(t ； r) (；Acceptsε .t .r p₁ p₂)) = ；Acceptsε (s ∪ t) r (∪Acceptsεʳ s t p₁) p₂
  ⟨ x ∷ xs ⟩-；-distribʳ-∪ r s t with acceptsε? s | acceptsε? t | acceptsε? (s ∪ t)
  ... | yes p | yes q | yes pq = begin
    (δ x r ∪ ((δ x s ∪ δ x t) ； r)) ≈⟨ ⟨ xs ⟩-∪-cong ⟨ xs ⟩≈RL-refl (⟨ xs ⟩-；-distribʳ-∪ r (δ x s) (δ x t)) ⟩
    (δ x r ∪ ((δ x s ； r) ∪ (δ x t ； r))) ≈⟨ prove 3 (v₁ ⊕ (v₂ ⊕ v₃)) ((v₁ ⊕ v₂) ⊕ (v₁ ⊕ v₃)) (δ x r ∷ (δ x s ； r) ∷ (δ x t ； r) ∷ []) ⟩
    ((δ x r ∪ (δ x s ； r)) ∪ (δ x r ∪ (δ x t ； r))) ∎
    where
      open SetoidReasoning ⟨ xs ⟩RL-setoid
      open ICMSolver ⟨ xs ⟩-∪-idempotentCommutativeMonoid
      v₁ = var zero
      v₂ = var (suc zero)
      v₃ = var (suc (suc zero))
  ... | yes p | no ¬q | yes pq = begin
    (δ x r ∪ ((δ x s ∪ δ x t) ； r)) ≈⟨ ⟨ xs ⟩-∪-cong ⟨ xs ⟩≈RL-refl (⟨ xs ⟩-；-distribʳ-∪ r (δ x s) (δ x t)) ⟩
    (δ x r ∪ ((δ x s ； r) ∪ (δ x t ； r))) ≈˘⟨ ⟨ xs ⟩-∪-assoc (δ x r) (δ x s ； r) (δ x t ； r) ⟩
    ((δ x r ∪ (δ x s ； r)) ∪ (δ x t ； r)) ∎
    where
      open SetoidReasoning ⟨ xs ⟩RL-setoid
  ... | yes p | yes q | no ¬pq = ⊥-elim (¬pq (∪Acceptsεˡ s t p))
  ... | yes p | no ¬q | no ¬pq = ⊥-elim (¬pq (∪Acceptsεˡ s t p))
  ... | no ¬p | yes q | yes pq = begin
    δ x r ∪ ((δ x s ∪ δ x t) ； r) ≈⟨ ⟨ xs ⟩-∪-cong ⟨ xs ⟩≈RL-refl (⟨ xs ⟩-；-distribʳ-∪ r (δ x s) (δ x t)) ⟩
    δ x r ∪ ((δ x s ； r) ∪ (δ x t ； r)) ≈⟨ prove 3 (v₁ ⊕ (v₂ ⊕ v₃)) (v₂ ⊕ (v₁ ⊕ v₃)) (δ x r ∷ (δ x s ； r) ∷ (δ x t ； r) ∷ []) ⟩
    (δ x s ； r) ∪ (δ x r ∪ (δ x t ； r)) ∎
    where
      open SetoidReasoning ⟨ xs ⟩RL-setoid
      open CMSolver ⟨ xs ⟩-∪-commutativeMonoid
      v₁ = var zero
      v₂ = var (suc zero)
      v₃ = var (suc (suc zero))
  ... | no ¬p | yes q | no ¬pq = ⊥-elim (¬pq (∪Acceptsεʳ s t q))
  ... | no ¬p | no ¬q | yes (∪Acceptsεˡ .s .t p) = ⊥-elim (¬p p)
  ... | no ¬p | no ¬q | yes (∪Acceptsεʳ .s .t q) = ⊥-elim (¬q q)
  ... | no ¬p | no ¬q | no ¬pq = ⟨ xs ⟩-；-distribʳ-∪ r (δ x s) (δ x t)

  ⟨_⟩-；-assoc : ∀ xs → Associative ⟨ xs ⟩_≈RL_ _；_
  ⟨ [] ⟩-；-assoc r s t = lemma₁ , lemma₂
    where
      lemma₁ : Accepts ((r ； s) ； t) [] → Accepts (r ； (s ； t)) []
      lemma₁ (；Acceptsε .(r ； s) .t (；Acceptsε .r .s p₁ p₂) p₃) = ；Acceptsε r (s ； t) p₁ (；Acceptsε s t p₂ p₃)

      lemma₂ : Accepts (r ； (s ； t)) [] → Accepts ((r ； s) ； t) []
      lemma₂ (；Acceptsε . r .(s ； t) p₁ (；Acceptsε .s .t p₂ p₃)) = ；Acceptsε (r ； s) t (；Acceptsε r s p₁ p₂) p₃
  ⟨ x ∷ xs ⟩-；-assoc r s t with acceptsε? r in rr | acceptsε? s in ss
  ... | yes p | yes q rewrite rr rewrite ss = begin
    (δ x t ∪ ((δ x s ∪ (δ x r ； s)) ； t)) ≈⟨ ⟨ xs ⟩-∪-cong ⟨ xs ⟩≈RL-refl (⟨ xs ⟩-；-distribʳ-∪ t (δ x s) (δ x r ； s)) ⟩
    (δ x t ∪ ((δ x s ； t) ∪ ((δ x r ； s) ； t))) ≈˘⟨ ⟨ xs ⟩-∪-assoc (δ x t) (δ x s ； t) ((δ x r ； s) ； t) ⟩
    ((δ x t ∪ (δ x s ； t)) ∪ ((δ x r ； s) ； t)) ≈⟨ ⟨ xs ⟩-∪-cong ⟨ xs ⟩≈RL-refl (⟨ xs ⟩-；-assoc (δ x r) s t) ⟩
    ((δ x t ∪ (δ x s ； t)) ∪ (δ x r ； (s ； t))) ∎
    where
      open SetoidReasoning ⟨ xs ⟩RL-setoid
  ... | yes p | no ¬q rewrite rr rewrite ss = begin
    ((δ x s ∪ (δ x r ； s)) ； t) ≈⟨ ⟨ xs ⟩-；-distribʳ-∪ t (δ x s) (δ x r ； s) ⟩
    ((δ x s ； t) ∪ ((δ x r ； s) ； t)) ≈⟨ ⟨ xs ⟩-∪-cong ⟨ xs ⟩≈RL-refl (⟨ xs ⟩-；-assoc (δ x r) s t) ⟩
    ((δ x s ； t) ∪ (δ x r ； (s ； t))) ∎
    where
      open SetoidReasoning ⟨ xs ⟩RL-setoid
  ... | no ¬p | yes q rewrite rr = ⟨ xs ⟩-；-assoc (δ x r) s t
  ... | no ¬p | no ¬q rewrite rr = ⟨ xs ⟩-；-assoc (δ x r) s t

  ⟨_⟩-；-zeroˡ : ∀ xs → LeftZero ⟨ xs ⟩_≈RL_ ∅ _；_
  ⟨ [] ⟩-；-zeroˡ r = lemma₁ , lemma₂
    where
      lemma₁ : Accepts (∅ ； r) [] → Accepts ∅ []
      lemma₁ (；Acceptsε .∅ .r () _)

      lemma₂ : Accepts ∅ [] → Accepts (∅ ； r) []
      lemma₂ ()
  ⟨ x ∷ xs ⟩-；-zeroˡ r with acceptsε? ∅
  ... | no ¬p = ⟨ xs ⟩-；-zeroˡ r

  ⟨_⟩-；-zeroʳ : ∀ xs → RightZero ⟨ xs ⟩_≈RL_ ∅ _；_
  ⟨ [] ⟩-；-zeroʳ r = lemma₁ , lemma₂
    where
      lemma₁ : Accepts (r ； ∅) [] → Accepts ∅ []
      lemma₁ (；Acceptsε .r .∅ _ ())

      lemma₂ : Accepts ∅ [] → Accepts (r ； ∅) []
      lemma₂ ()
  ⟨ x ∷ xs ⟩-；-zeroʳ r with acceptsε? r
  ... | yes p = begin
    (∅ ∪ (δ x r ； ∅)) ≈⟨ ⟨ xs ⟩-∪-identityˡ (δ x r ； ∅) ⟩
    (δ x r ； ∅) ≈⟨ ⟨ xs ⟩-；-zeroʳ (δ x r) ⟩
    ∅ ∎
    where
      open SetoidReasoning ⟨ xs ⟩RL-setoid
  ... | no ¬p = ⟨ xs ⟩-；-zeroʳ (δ x r)

  ⟨_⟩-；-identityˡ : ∀ xs → LeftIdentity ⟨ xs ⟩_≈RL_ (∅ ⋆) _；_
  ⟨ [] ⟩-；-identityˡ r = lemma₁ , lemma₂
    where
      lemma₁ : Accepts ((∅ ⋆) ； r) [] → Accepts r []
      lemma₁ (；Acceptsε .(∅ ⋆) .r (⋆Acceptsε .∅) p) = p

      lemma₂ : Accepts r [] → Accepts ((∅ ⋆) ； r) []
      lemma₂ p = ；Acceptsε (∅ ⋆) r (⋆Acceptsε ∅) p
  ⟨ x ∷ xs ⟩-；-identityˡ r with acceptsε? (∅ ⋆)
  ... | yes p = begin
    (δ x r ∪ ((∅ ； (∅ ⋆)) ； r)) ≈⟨ ⟨ xs ⟩-∪-cong ⟨ xs ⟩≈RL-refl (⟨ xs ⟩-；-assoc ∅ (∅ ⋆) r) ⟩
    (δ x r ∪ (∅ ； ((∅ ⋆) ； r))) ≈⟨ ⟨ xs ⟩-∪-cong ⟨ xs ⟩≈RL-refl (⟨ xs ⟩-；-zeroˡ ((∅ ⋆) ； r)) ⟩
    (δ x r ∪ ∅) ≈⟨ ⟨ xs ⟩-∪-identityʳ (δ x r) ⟩
    δ x r ∎
    where
      open SetoidReasoning ⟨ xs ⟩RL-setoid
  ... | no ¬p = ⊥-elim (¬p (⋆Acceptsε ∅))

  ⟨_⟩-；-identityʳ : ∀ xs → RightIdentity ⟨ xs ⟩_≈RL_ (∅ ⋆) _；_
  ⟨ [] ⟩-；-identityʳ r = lemma₁ , lemma₂
    where
      lemma₁ : Accepts (r ； (∅ ⋆)) [] → Accepts r []
      lemma₁ (；Acceptsε .r .(∅ ⋆) p (⋆Acceptsε .∅)) = p

      lemma₂ : Accepts r [] → Accepts (r ； (∅ ⋆)) []
      lemma₂ p = ；Acceptsε r (∅ ⋆) p (⋆Acceptsε ∅)
  ⟨ x ∷ xs ⟩-；-identityʳ r with acceptsε? r
  ... | yes p = begin
    ((∅ ； (∅ ⋆)) ∪ (δ x r ； (∅ ⋆))) ≈⟨ ⟨ xs ⟩-∪-cong (⟨ xs ⟩-；-zeroˡ (∅ ⋆)) ⟨ xs ⟩≈RL-refl ⟩
    (∅ ∪ (δ x r ； (∅ ⋆))) ≈⟨ ⟨ xs ⟩-∪-identityˡ (δ x r ； (∅ ⋆)) ⟩
    (δ x r ； (∅ ⋆)) ≈⟨ ⟨ xs ⟩-；-identityʳ (δ x r) ⟩
    δ x r ∎
    where
      open SetoidReasoning ⟨ xs ⟩RL-setoid
  ... | no ¬p = ⟨ xs ⟩-；-identityʳ (δ x r)

module _ where
  open Algebra.Definitions _≈RL_
  open Algebra.Structures _≈RL_

  ∪-cong : Congruent₂ _∪_
  ∪-cong x≈y u≈v xs = ⟨ xs ⟩-∪-cong (x≈y xs) (u≈v xs)

  ∪-assoc : Associative _∪_
  ∪-assoc r s t xs = ⟨ xs ⟩-∪-assoc r s t

  ∪-comm : Commutative _∪_
  ∪-comm r s xs = ⟨ xs ⟩-∪-comm r s

  ∪-identityˡ : LeftIdentity ∅ _∪_
  ∪-identityˡ r xs = ⟨ xs ⟩-∪-identityˡ r

  ∪-identityʳ : RightIdentity ∅ _∪_
  ∪-identityʳ r xs = ⟨ xs ⟩-∪-identityʳ r

  ∪-idem : Idempotent _∪_
  ∪-idem r xs = ⟨ xs ⟩-∪-idem r

  ∪-isMagma : IsMagma _∪_
  ∪-isMagma = record
    { isEquivalence = ≈RL-isEquivalence
    ; ∙-cong = ∪-cong
    }

  ∪-isSemigroup : IsSemigroup _∪_
  ∪-isSemigroup = record
    { isMagma = ∪-isMagma
    ; assoc = ∪-assoc
    }

  ∪-isBand : IsBand _∪_
  ∪-isBand = record
    { isSemigroup = ∪-isSemigroup
    ; idem = ∪-idem
    }

  ∪-isCommutativeSemigroup : IsCommutativeSemigroup _∪_
  ∪-isCommutativeSemigroup = record
    { isSemigroup = ∪-isSemigroup
    ; comm = ∪-comm
    }

  ∪-∅-isMonoid : IsMonoid _∪_ ∅
  ∪-∅-isMonoid = record
    { isSemigroup = ∪-isSemigroup
    ; identity = ∪-identityˡ , ∪-identityʳ
    }

  ∪-∅-isCommutativeMonoid : IsCommutativeMonoid _∪_ ∅
  ∪-∅-isCommutativeMonoid = record
    { isMonoid = ∪-∅-isMonoid
    ; comm = ∪-comm
    }

  ∪-∅-isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid _∪_ ∅
  ∪-∅-isIdempotentCommutativeMonoid = record
    { isCommutativeMonoid = ∪-∅-isCommutativeMonoid
    ; idem = ∪-idem
    }

  ∪-∅-commutativeMonoid : CommutativeMonoid c c
  ∪-∅-commutativeMonoid = record { isCommutativeMonoid = ∪-∅-isCommutativeMonoid }

  ；-cong : Congruent₂ _；_
  ；-cong {x} {y} {u} {v} x≈y u≈v [] = lemma₁ , lemma₂
    where
      lemma₁ : Accepts (x ； u) [] → Accepts (y ； v) []
      lemma₁ (；Acceptsε .x .u p q) = ；Acceptsε y v (proj₁ (x≈y []) p) (proj₁ (u≈v []) q)

      lemma₂ : Accepts (y ； v) [] → Accepts (x ； u) []
      lemma₂ (；Acceptsε .y .v p q) = ；Acceptsε x u (proj₂ (x≈y []) p) (proj₂ (u≈v []) q)
  ；-cong {x} {y} {u} {v} x≈y u≈v (a ∷ as) with acceptsε? x | acceptsε? y
  ... | yes p | yes q = begin
    (δ a u ∪ (δ a x ； u)) ≈⟨ ⟨ as ⟩-∪-cong (u≈v (a ∷ as)) (；-cong (λ as′ → x≈y (a ∷ as′)) u≈v as) ⟩
    (δ a v ∪ (δ a y ； v)) ∎
    where
      open SetoidReasoning ⟨ as ⟩RL-setoid
  ... | no ¬p | yes q = ⊥-elim (¬p (proj₂ (x≈y []) q))
  ... | yes p | no ¬q = ⊥-elim (¬q (proj₁ (x≈y []) p))
  ... | no ¬p | no ¬q = ；-cong (λ as′ → x≈y (a ∷ as′)) u≈v as

  ；-distribˡ-∪ : _；_ DistributesOverˡ _∪_
  ；-distribˡ-∪ r s t xs = ⟨ xs ⟩-；-distribˡ-∪ r s t

  ；-distribʳ-∪ : _；_ DistributesOverʳ _∪_
  ；-distribʳ-∪ r s t xs = ⟨ xs ⟩-；-distribʳ-∪ r s t

  ；-assoc : Associative _；_
  ；-assoc r s t xs = ⟨ xs ⟩-；-assoc r s t

  ；-zeroˡ : LeftZero ∅ _；_
  ；-zeroˡ r xs = ⟨ xs ⟩-；-zeroˡ r

  ；-zeroʳ : RightZero ∅ _；_
  ；-zeroʳ r xs = ⟨ xs ⟩-；-zeroʳ r

  ；-identityˡ : LeftIdentity (∅ ⋆) _；_
  ；-identityˡ r xs = ⟨ xs ⟩-；-identityˡ r

  ；-identityʳ : RightIdentity (∅ ⋆) _；_
  ；-identityʳ r xs = ⟨ xs ⟩-；-identityʳ r
