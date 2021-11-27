{-# OPTIONS --without-K #-}

open import Relation.Binary

module Regex.Properties {c ℓ} (Alphabet : DecSetoid c ℓ) where

open import Regex Alphabet

open import Algebra.Bundles
open import Algebra.Definitions _≈RL_
open import Algebra.Structures _≈RL_
import Algebra.Solver.CommutativeMonoid as CMSolver
open import Data.Fin.Base using (zero; suc)
open import Data.List
open import Data.Product
open import Data.Vec.Base using (_∷_; [])
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- is this what I want?
δ*-∪ : ∀ r s xs → δ* (r ∪ s) xs ≡ δ* r xs ∪ δ* s xs
δ*-∪ r s [] = refl
δ*-∪ r s (x ∷ xs) = δ*-∪ (δ x r) (δ x s) xs

-- _≈RL_ is an equivalence relation
≈RL-refl : Reflexive _≈RL_
≈RL-refl xs = (λ p → p) , λ p → p

≈RL-sym : Symmetric _≈RL_
≈RL-sym p xs = swap (p xs)

≈RL-trans : Transitive _≈RL_
≈RL-trans p q xs = (λ r → proj₁ (q xs) (proj₁ (p xs) r)) , λ r → proj₂ (p xs) (proj₂ (q xs) r)

≈RL-isEquivalence : IsEquivalence _≈RL_
≈RL-isEquivalence = record
  { refl = ≈RL-refl
  ; sym = ≈RL-sym
  ; trans = ≈RL-trans
  }

RL-setoid : Setoid c c
RL-setoid = record { isEquivalence = ≈RL-isEquivalence }

-- Algebraic properties of regular languages
∪-cong : Congruent₂ _∪_
∪-cong {x} {y} {u} {v} x≈y u≈v [] = lemma₁ , lemma₂
  where
    lemma₁ : Accepts (x ∪ u) [] → Accepts (y ∪ v) []
    lemma₁ (∪Acceptsεˡ .x .u p) = ∪Acceptsεˡ y v (proj₁ (x≈y []) p)
    lemma₁ (∪Acceptsεʳ .x .u p) = ∪Acceptsεʳ y v (proj₁ (u≈v []) p)

    lemma₂ : Accepts (y ∪ v) [] → Accepts (x ∪ u) []
    lemma₂ (∪Acceptsεˡ .y .v p) = ∪Acceptsεˡ x u (proj₂ (x≈y []) p)
    lemma₂ (∪Acceptsεʳ .y .v p) = ∪Acceptsεʳ x u (proj₂ (u≈v []) p)
∪-cong p q (a ∷ as) = ∪-cong (λ as′ → p (a ∷ as′)) (λ as′ → q (a ∷ as′)) as

∪-assoc : Associative _∪_
∪-assoc r s t [] = lemma₁ , lemma₂
  where
    lemma₁ : Accepts ((r ∪ s) ∪ t) [] → Accepts (r ∪ (s ∪ t)) []
    lemma₁ (∪Acceptsεˡ .(r ∪ s) .t (∪Acceptsεˡ .r .s p)) = ∪Acceptsεˡ r (s ∪ t) p
    lemma₁ (∪Acceptsεˡ .(r ∪ s) .t (∪Acceptsεʳ .r .s p)) = ∪Acceptsεʳ r (s ∪ t) (∪Acceptsεˡ s t p)
    lemma₁ (∪Acceptsεʳ .(r ∪ s) .t p) = ∪Acceptsεʳ r (s ∪ t) (∪Acceptsεʳ s t p)

    lemma₂ : Accepts (r ∪ (s ∪ t)) [] → Accepts ((r ∪ s) ∪ t) []
    lemma₂ (∪Acceptsεˡ .r .(s ∪ t) p) = ∪Acceptsεˡ (r ∪ s) t (∪Acceptsεˡ r s p)
    lemma₂ (∪Acceptsεʳ .r .(s ∪ t) (∪Acceptsεˡ .s .t p)) = ∪Acceptsεˡ (r ∪ s) t (∪Acceptsεʳ r s p)
    lemma₂ (∪Acceptsεʳ .r .(s ∪ t) (∪Acceptsεʳ .s .t p)) = ∪Acceptsεʳ (r ∪ s) t p
∪-assoc r s t (x ∷ xs) = ∪-assoc (δ x r) (δ x s) (δ x t) xs

∪-comm : Commutative _∪_
∪-comm r s [] = lemma₁ , lemma₂
  where
    lemma₁ : Accepts (r ∪ s) [] → Accepts (s ∪ r) []
    lemma₁ (∪Acceptsεˡ .r .s x) = ∪Acceptsεʳ s r x
    lemma₁ (∪Acceptsεʳ .r .s x) = ∪Acceptsεˡ s r x

    lemma₂ : Accepts (s ∪ r) [] → Accepts (r ∪ s) []
    lemma₂ (∪Acceptsεˡ .s .r x) = ∪Acceptsεʳ r s x
    lemma₂ (∪Acceptsεʳ .s .r x) = ∪Acceptsεˡ r s x
∪-comm r s (x ∷ xs) = ∪-comm (δ x r) (δ x s) xs

∪-identityˡ : LeftIdentity ∅ _∪_
∪-identityˡ r [] = lemma₁ , lemma₂
  where
    lemma₁ : Accepts (∅ ∪ r) [] → Accepts r []
    lemma₁ (∪Acceptsεʳ .∅ .r p) = p

    lemma₂ : Accepts r [] → Accepts (∅ ∪ r) []
    lemma₂ p = ∪Acceptsεʳ ∅ r p
∪-identityˡ r (x ∷ xs) = ∪-identityˡ (δ x r) xs

∪-identityʳ : RightIdentity ∅ _∪_
∪-identityʳ r [] = lemma₁ , lemma₂
  where
    lemma₁ : Accepts (r ∪ ∅) [] → Accepts r []
    lemma₁ (∪Acceptsεˡ .r .∅ p) = p

    lemma₂ : Accepts r [] → Accepts (r ∪ ∅) []
    lemma₂ p = ∪Acceptsεˡ r ∅ p
∪-identityʳ r (x ∷ xs) = ∪-identityʳ (δ x r) xs

∪-idempotent : Idempotent _∪_
∪-idempotent r [] = lemma₁ , lemma₂
  where
    lemma₁ : Accepts (r ∪ r) [] → Accepts r []
    lemma₁ (∪Acceptsεˡ .r .r p) = p
    lemma₁ (∪Acceptsεʳ .r .r p) = p

    lemma₂ : Accepts r [] → Accepts (r ∪ r) []
    lemma₂ p = ∪Acceptsεˡ r r p
∪-idempotent r (x ∷ xs) = ∪-idempotent (δ x r) xs

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
  ; idem = ∪-idempotent
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
  ; idem = ∪-idempotent
  }

∪-∅-commutativeMonoid : CommutativeMonoid c c
∪-∅-commutativeMonoid = record { isCommutativeMonoid = ∪-∅-isCommutativeMonoid }

{-# TERMINATING #-} -- this shouldn't be necessary!
；-distribˡ-∪ : _；_ DistributesOverˡ _∪_
；-distribˡ-∪ r s t [] = lemma₁ , lemma₂
  where
    lemma₁ : Accepts (r ； (s ∪ t)) [] → Accepts ((r ； s) ∪ (r ； t)) []
    lemma₁ (；Acceptsε .r .(s ∪ t) p₁ (∪Acceptsεˡ .s .t p₂)) = ∪Acceptsεˡ (r ； s) (r ； t) (；Acceptsε r s p₁ p₂)
    lemma₁ (；Acceptsε .r .(s ∪ t) p₁ (∪Acceptsεʳ .s .t p₂)) = ∪Acceptsεʳ (r ； s) (r ； t) (；Acceptsε r t p₁ p₂)

    lemma₂ : Accepts ((r ； s) ∪ (r ； t)) [] → Accepts (r ； (s ∪ t)) []
    lemma₂ (∪Acceptsεˡ .(r ； s) .(r ； t) (；Acceptsε .r .s p₁ p₂)) = ；Acceptsε r (s ∪ t) p₁ (∪Acceptsεˡ s t p₂)
    lemma₂ (∪Acceptsεʳ .(r ； s) .(r ； t) (；Acceptsε .r .t p₁ p₂)) = ；Acceptsε r (s ∪ t) p₁ (∪Acceptsεʳ s t p₂)
；-distribˡ-∪ r s t (x ∷ xs) with acceptsε? r
... | yes _ = (begin
  ((δ x s ∪ δ x t) ∪ (δ x r ； (s ∪ t))) ≈⟨ ∪-cong ≈RL-refl (；-distribˡ-∪ (δ x r) s t) ⟩ -- Agda can't infer that this step is sound, because it's far away from the xs
  ((δ x s ∪ δ x t) ∪ ((δ x r ； s) ∪ (δ x r ； t))) ≈⟨ prove 4 ((v₁ ⊕ v₂) ⊕ (v₃ ⊕ v₄)) ((v₁ ⊕ v₃) ⊕ (v₂ ⊕ v₄)) (δ x s ∷ δ x t ∷ (δ x r ； s) ∷ (δ x r ； t) ∷ []) ⟩
  ((δ x s ∪ (δ x r ； s)) ∪ (δ x t ∪ (δ x r ； t))) ∎) xs
  where
    open SetoidReasoning RL-setoid
    open CMSolver ∪-∅-commutativeMonoid
    v₁ = var zero
    v₂ = var (suc zero)
    v₃ = var (suc (suc zero))
    v₄ = var (suc (suc (suc zero)))
... | no  _ = ；-distribˡ-∪ (δ x r) s t xs
