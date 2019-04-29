module cantor where

open import Data.Nat
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Function
open import Relation.Binary.PropositionalEquality

_⇒inj_ : Set → Set → Set
A ⇒inj B = Σ (A → B) λ f → (a a' : A) → f a ≡ f a' → a ≡ a'

someSet : ℕ → (ℕ → Bool)
someSet zero = λ zero → false
someSet (suc n) = {!λ n → someSet (not ?)!}

Cantor : (ℕ → Bool) ⇒inj ℕ → ⊥
Cantor f = {!λ x → ?!}
