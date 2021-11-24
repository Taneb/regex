{-# OPTIONS --safe --without-K #-}

open import Relation.Binary

module Regex.Properties {c ℓ} (Alphabet : DecSetoid c ℓ) where

open import Regex Alphabet

open import Algebra.Definitions _≈RL_
open import Data.List
open import Data.Product
open import Relation.Nullary
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

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
-- (δ x s ∪ δ x t) ∪ (δ x r ； (s ∪ t))
-- (δ x s ∪ δ x t) ∪ ((δ x r ； s) ∪ (δ x r ； t))
-- ((δ x s ∪ δ x t) ∪ (δ x r ； s)) ∪ (δ x r ； t)
-- (δ x s ∪ (δ x t ∪ (δ x r ； s))) ∪ (δ x r ； t)
-- (δ x s ∪ ((δ x r ； s) ∪ δ x t)) ∪ (δ x r ； t)
-- ((δ x s ∪ (δ x r ； s)) ∪ δ x t) ∪ (δ x r ； t)
-- (δ x s ∪ (δ x r ； s)) ∪ (δ x t ∪ (δ x r ； t))
... | yes _ = lemma₁ , lemma₂
  where
    lemma₁ : Accepts ((δ x s ∪  δ x t) ∪ (δ x r ； (s ∪ t))) xs → Accepts ((δ x s ∪ (δ x r ； s)) ∪ (δ x t ∪ (δ x r ； t))) xs
    lemma₁ p = {!proj₁ (；-distribˡ-∪ (δ x r) s t xs)!}

    lemma₂ : Accepts ((δ x s ∪ (δ x r ； s)) ∪ (δ x t ∪ (δ x r ； t))) xs → Accepts ((δ x s ∪ δ x t) ∪ (δ x r ； (s ∪ t))) xs
    lemma₂ p = {!proj₂ (；-distribˡ-∪ (δ x r) s t xs)!}
... | no  _ = ；-distribˡ-∪ (δ x r) s t xs

；-assoc : Associative _；_
；-assoc r s t [] = lemma₁ , lemma₂
  where
    lemma₁ : Accepts ((r ； s) ； t) [] → Accepts (r ； (s ； t)) []
    lemma₁ (；Acceptsε .(r ； s) .t (；Acceptsε .r .s p₁ p₂) p₃) = ；Acceptsε r (s ； t) p₁ (；Acceptsε s t p₂ p₃)

    lemma₂ : Accepts (r ； (s ； t)) [] → Accepts ((r ； s) ； t) []
    lemma₂ (；Acceptsε .r .(s ； t) p₁ (；Acceptsε .s .t p₂ p₃)) = ；Acceptsε (r ； s) t (；Acceptsε r s p₁ p₂) p₃
；-assoc r s t (x ∷ xs) with acceptsε? r in rr
... | no ¬p rewrite rr = ；-assoc (δ x r) s t xs
... | yes p with acceptsε? s in ss
--   Accepts (δ x t ∪ ((δ x s ∪ (δ x r ； s)) ； t)) xs
-- ↔ Accepts ((δ x t ∪ (δ x s ； t)) ∪ (δ x r ； (s ； t))) xs

--    δ x t ∪ ((δ x s ∪ (δ x r ； s)) ； t)
-- ≈ (δ x t ∪ (δ x s ； t)) ∪ (δ x r ； (s ； t))


-- δ x t ∪ ((δ x s ∪ (δ x r ； s)) ； t)
--   by ∪-cong ∪-distrib-；
-- δ x t ∪ ((δ x s ； t) ∪ ((δ x r ； s) ； t))
--
-- δ x t ∪ ((δ x s ； t) ∪ (δ x r ； (s ； t)))
--
-- (δ x t ∪ (δ x s ； t)) ∪ (δ x r ； (s ； t))

... | yes q rewrite rr rewrite ss = {!!}
... | no ¬q = {!!}

