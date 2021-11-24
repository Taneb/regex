{-# OPTIONS --safe --without-K #-}

open import Relation.Binary

module Regex {c ℓ} (Alphabet : DecSetoid c ℓ) where

open import Data.List.Base
open import Data.Product
open import Level
open import Relation.Nullary
open import Relation.Unary as Unary hiding (∅; _∪_)

open DecSetoid Alphabet renaming (Carrier to A)

data RegularLanguage : Set c where
  ∅ : RegularLanguage
  lit : A → RegularLanguage
  _⋆ : RegularLanguage → RegularLanguage
  _∪_ : RegularLanguage → RegularLanguage → RegularLanguage
  _；_ : RegularLanguage → RegularLanguage → RegularLanguage

-- Does this regular expression accept the empty string?
data Acceptsε : RegularLanguage → Set c where
  -- for all r, r⋆ accepts the empty string
  ⋆Acceptsε : ∀ r → Acceptsε (r ⋆)
  -- if s accepts the empty string, s ∪ r accepts the empty string
  ∪Acceptsεˡ : ∀ s r → Acceptsε s → Acceptsε (s ∪ r)
  -- if r accepts the empty string, s ∪ r accepts the empty string
  ∪Acceptsεʳ : ∀ s r → Acceptsε r → Acceptsε (s ∪ r)
  -- if both s and r accept the empty string, then s ； r accepts the empty string
  ；Acceptsε : ∀ s r → Acceptsε s → Acceptsε r → Acceptsε (s ； r)
  -- ∅ does not accept the empty string as it does not accept anything
  -- lit x does not accept the empty string as it only accepts x

acceptsε? : Unary.Decidable Acceptsε
acceptsε? ∅ = no (λ ())
acceptsε? (lit x) = no (λ ())
acceptsε? (x ⋆) = yes (⋆Acceptsε x)
acceptsε? (s ∪ r) with acceptsε? s | acceptsε? r
... | yes p | q = yes (∪Acceptsεˡ s r p)
... | no ¬p | yes q = yes (∪Acceptsεʳ s r q)
... | no ¬p | no ¬q = no λ { (∪Acceptsεˡ .s .r p) → ¬p p; (∪Acceptsεʳ .s .r q) → ¬q q }
acceptsε? (s ； r) with acceptsε? s | acceptsε? r
... | yes p | yes q = yes (；Acceptsε s r p q)
... | no ¬p | q = no λ { (；Acceptsε .s .r p _) → ¬p p }
... | yes p | no ¬q = no λ { (；Acceptsε .s .r _ q) → ¬q q }

δ : A → RegularLanguage → RegularLanguage
δ x ∅ = ∅
δ x (lit c) with x ≟ c
... | yes _ = ∅ ⋆
... | no  _ = ∅
δ x (r ⋆) = δ x r ； (r ⋆)
δ x (s ∪ r) = δ x s ∪ δ x r
δ x (s ； r) with acceptsε? s
... | yes _ = δ x r ∪ (δ x s ； r)
... | no  _ = δ x s ； r

δ* : RegularLanguage → List A → RegularLanguage
δ* r [] = r
δ* r (x ∷ xs) = δ* (δ x r) xs

Accepts : RegularLanguage → List A → Set c
Accepts r xs = Acceptsε (δ* r xs)

accepts? : (r : RegularLanguage) (xs : List A) → Dec (Accepts r xs)
accepts? r xs = acceptsε? (δ* r xs)

_≈RL_ : Rel RegularLanguage c
s ≈RL r = ∀ xs → (Accepts s xs → Accepts r xs) × (Accepts r xs → Accepts s xs)

