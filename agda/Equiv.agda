{-# OPTIONS --without-K --safe #-}

module Equiv where

open import Prelude

open import Syntax

-- pairs of ids with their canonical id
Canon : Type
Canon = List (UConst × UConst)

canon : Canon → UConst → UConst
canon []             i = i -- not found, so is its own representative
canon ((j , c) ∷ cs) i = if j == i then c else canon cs i

_⋆_ : ℕ → ℕ → ℕ
zero  ⋆ n     = n
suc m ⋆ zero  = suc m
suc m ⋆ suc n = suc zero

open import Relation.Binary.PropositionalEquality

⋆assoc : (a b c : ℕ) → (a ⋆ b) ⋆ c ≡ a ⋆ (b ⋆ c)
⋆assoc zero zero c             = refl
⋆assoc zero (suc b) zero       = refl
⋆assoc zero (suc b) (suc c)    = refl
⋆assoc (suc a) zero c          = refl
⋆assoc (suc a) (suc b) zero    = refl
⋆assoc (suc a) (suc b) (suc c) = refl

⋆comm : (a b  : ℕ) → a ⋆ b ≡ b ⋆ a
⋆comm zero zero       = refl
⋆comm zero (suc b)    = refl
⋆comm (suc a) zero    = refl
⋆comm (suc a) (suc b) = refl
