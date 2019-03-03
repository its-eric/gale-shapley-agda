module Acc where

open import Data.Nat
open import Relation.Binary.Core
open import Relation.Nullary
open import Agda.Builtin.Equality

-- http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.32.6626&rep=rep1&type=pdf

-- _∸_

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

{- Something like this is defined in the stdlib:
_<?_ : Decidable _<_
x <? y = suc x ≤? y 
-}

-< : {n m : ℕ} → ¬ (n < suc m) → n ∸ suc m < n
-< = {!!}

trans : Transitive _≤_
trans z≤n       _         = z≤n
trans (s≤s m≤n) (s≤s n≤o) = s≤s (trans m≤n n≤o)


{-
mod : ℕ → ℕ → Maybe ℕ
mod n zero = Nothing
mod n (suc m) with n <? suc m
mod n (suc m) | yes p = Just n
mod n (suc m) | no ¬p = mod (n ∸ suc m) (suc m)
-}
{-
data Acc (A : Set)(_≺_ : A → A → Set) : A → Set where
  acc : (a : A)(p : (x : A)(h : x ≺ a) → Acc A _≺_ x) → Acc A _≺_ a

mod : (n m : ℕ) → Acc ℕ _<_ n → Maybe ℕ
mod n zero h = Nothing
mod n (suc m) (acc .n hl) with n <? suc m
mod n (suc m) (acc .n hl) | yes h = Just n
mod n (suc m) (acc .n hl) | no  h = mod (n ∸ suc m) (suc m) (hl (n ∸ suc m) (-< h))
-}

data Acc : ℕ → Set where
  acc : (a : ℕ)(p : (x : ℕ)(h : x < a) → Acc x) → Acc a

mod' : (n m : ℕ) → Acc n → Maybe ℕ
mod' n zero h = Nothing
mod' n (suc m) (acc .n hl) with n <? suc m
mod' n (suc m) (acc .n hl) | yes h = Just n
mod' n (suc m) (acc .n hl) | no  h = mod' (n ∸ suc m) (suc m) (hl (n ∸ suc m) (-< h))

allacc : (n : ℕ) → Acc n
allacc zero = acc zero λ _ ()
allacc (suc n) with allacc n
allacc (suc n) | acc .n p = {!!}

{--
acc _ f
  where
    f : (x : ℕ) → suc x ≤ suc n → Acc x
    f zero p = acc zero λ _ ()
    f (suc x) (s≤s h) = acc {!!} {!!}
-}

mod : ℕ → ℕ → Maybe ℕ
mod n m = mod' n m (allacc n)

data ModAcc : (n m : ℕ) → Set where
  modAcc0 : (n : ℕ) → ModAcc n zero
  modAcc< : {n m : ℕ} → (p : n < m) → ModAcc n m 
  modAcc≤ : {n m : ℕ} → ¬ (m ≡ 0) → ¬ (n < m) → ModAcc (n ∸ m) m →  ModAcc n m

betterMod : (n m : ℕ) → ModAcc n m → Maybe ℕ
-- The case when m is zero : error
betterMod n .0 (modAcc0 .n) = Nothing
-- The case when n < m. h1 is a proof of that.
betterMod n m (modAcc< h1) = Just n
-- h is a proof that m ≠ 0.
-- h1 is a proof that n ≥ m.
-- h2 is the complicated proof, that ModAcc is satisfied by (n - m, m) 
betterMod n m (modAcc≤ h h1 h2) = betterMod (n ∸ m) m h2
