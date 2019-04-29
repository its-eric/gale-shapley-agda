module Practice where

open import Data.List
open import Data.Nat
open import Data.Bool
open import Agda.Builtin.Equality

-- Here is a simple theorem we can prove involving both the length function and
-- list append (_++_):
length-++ : ∀{l}{A : Set l}(l1 l2 : List A) → length (l1 ++ l2) ≡ (length l1) + (length l2)
length-++ [] l2 = refl
length-++ (h ∷ t) l2 rewrite length-++ t l2 = refl

++-assoc : ∀{l}{A : Set l}(l1 : List A)(l2 : List A)(l3 : List A) →
           (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
++-assoc [] l2 l3 = refl
++-assoc (x ∷ xs) l2 l3 rewrite ++-assoc xs l2 l3 = refl

length-filter : ∀{l}{A : Set l}(p : A → Bool)(l : List A) →
                (length (filter p l) ≤ length l) ≡ true
length-filter p [] = refl
length-filter p (x ∷ l) with p x
length-filter p (x ∷ l) | true   = length-filter p l
length-filter p (x ∷ l) | false  = ?
