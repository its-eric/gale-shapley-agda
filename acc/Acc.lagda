\newcommand{\AccAgda}{%

This implementation is based on the paper by Ana Bove \cite{Bove2002SimpleTheory}.

\begin{code}

module Acc where

open import Data.Nat
open import Data.Empty
open import Function
open import Induction
open import Induction.WellFounded
open import Relation.Binary.Core
open import Relation.Nullary
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

-- Something like this is defined in the stdlib:
-- _<?_ : Decidable _<_
-- x <? y = suc x ≤? y 

-- That is a help for "it is decidable whether a
-- natural number is less than another".

-- The following lemma -< says if a natural number n is
-- not less than another one (not zero)
-- then the result of subtracting the second from the first
-- is less than the first.
-< : {n m : ℕ} → ¬ (n < suc m) → n ∸ suc m < n
-< = λ p → {!!}

-- This could help perhaps...
trans : Transitive _≤_
trans z≤n       _         = z≤n
trans (s≤s m≤n) (s≤s n≤o) = s≤s (trans m≤n n≤o)

-- First we try to prove accessibility using a standard predicate.

-- The Haskell version of the mod algorithm would go something like this:

-- mod : ℕ → ℕ → Maybe ℕ
-- mod n zero = Nothing
-- mod n (suc m) with n <? suc m
-- mod n (suc m) | yes p = Just n
-- mod n (suc m) | no ¬p = mod (n ∸ suc m) (suc m)

mod' : (n m : ℕ) → Acc _<_ n → Maybe ℕ
mod' n zero h = Nothing
mod' n (suc m) (acc h₁) with n <? suc m
... | yes h = Just n
... | no  h = mod' (n ∸ suc m) (suc m) (h₁ (n ∸ suc m) (-< h))

allAcc : (n : ℕ) → Acc _<_ n
allAcc zero    = acc λ _ ()
allAcc (suc n) with allAcc n
allAcc (suc n) | acc h = acc f
  where
    f : (x : ℕ) → suc x ≤ suc n → Acc _<_ x
    -- Next task: define this function
    f = {!!}

mod : ℕ → ℕ → Maybe ℕ
mod n m = mod' n m (allAcc n)

-- From here on we use Bove's method for writing a
-- special accessibility predicate.

data ModAcc : (n m : ℕ) → Set where
  modAcc0 : (n : ℕ) → ModAcc n zero
  modAcc< : {n m : ℕ} → (p : n < m) → ModAcc n m 
  modAcc≤ : {n m : ℕ} → ¬ (m ≡ 0) → ¬ (n < m) →
            ModAcc (n ∸ m) m →  ModAcc n m

betterMod : (n m : ℕ) → ModAcc n m → Maybe ℕ
-- The case when m is zero : error
betterMod n .0 (modAcc0 .n) = Nothing
-- The case when n < m. h₁ is a proof of that.
betterMod n m (modAcc< h₁) = Just n
-- h is a proof that m ≠ 0.
-- h₁ is a proof that n ≥ m.
-- h₂ is the complicated proof, that ModAcc is satisfied by (n - m, m) 
betterMod n m (modAcc≤ h h₁ h₂) = betterMod (n ∸ m) m h₂

modAccAux : (m p : ℕ) → Acc _<_ p → (f : (q : ℕ) → (q < p) →
            ModAcc q m) → ModAcc p m
modAccAux zero p h f = modAcc0 p
modAccAux (suc n) p h f with p <? suc n
... | yes h₁ = modAcc< h₁
... | no  h₁ = modAcc≤ ({!!}) h₁ (f (p ∸ suc n) (-< h₁))

Pₙ : {n m : ℕ} → ∀ n m → ModAcc n m 
Pₙ n zero    = modAcc0 n
Pₙ n (suc m) with n <? suc m
... | yes h = modAcc< h
... | no  h = modAccAux (suc m) n (allAcc n) f where
  f : (q : ℕ) → suc q ≤ n → ModAcc q (suc m)
  f zero    (s≤s h) = modAcc< {!!}
  f (suc q) (s≤s h) = modAcc< {!!}
  
allModAcc : (n m : ℕ) → ModAcc n m
allModAcc n m = Pₙ n m

finalMod : (n m : ℕ) → Maybe ℕ
finalMod n m = betterMod n m (allModAcc n m)

\end{code}}
