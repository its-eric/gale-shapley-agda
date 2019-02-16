module GaleShapley where

open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Bool
open import Data.List
open import Relation.Nullary

record MatchingState : Set where
  constructor mkState
  field
    freeMen : List (ℕ × List ℕ)
    engagedMen : List (ℕ × List ℕ)
    women : List (ℕ × List ℕ)
    couples : List (ℕ × ℕ)

{-# TERMINATING #-}
f : ℕ → ℕ
f zero = 3
f (suc n) = f (suc (suc n))

-- Code by @yeputons on Stack Overflow :D
is-≤ : ℕ → ℕ → Bool
is-≤ a b with a ≤? b
... | Dec.yes _ = true
... | Dec.no _ = false

positionInList : ℕ → List ℕ → ℕ → ℕ
positionInList x [] _ = zero --when the man is not in the list...??
positionInList x (xs ∷ xss) zero with compare x xs
... | equal _  = zero --found man at the tip of the list!
... | _        = positionInList x xss (suc zero) --accumulate and keep searching...
positionInList x (xs ∷ xss) (suc n) with compare x xs
... | equal _  = suc n --found man somewhere in the list
... | _        = positionInList x xss (suc (suc n)) --accumulate and keep searching

propose : ℕ → ℕ → List ℕ → Bool
-- If woman is with her most preferred husband, she simply always says no to further proposals.
propose man zero preferenceList = false
-- Otherwise she must compare
propose man (suc posCurrentHusband) preferenceList = is-≤ (positionInList man preferenceList zero) posCurrentHusband

-- We assume the "husbands" to be the proposing side,
-- therefore if women propose the pair looks like (wife, husband)
getHusband : ℕ → List (ℕ × ℕ) → ℕ
getHusband woman [] = zero --not married yet and this is the first proposal in the algorithm!
getHusband woman ((m , w) ∷ []) with compare woman w
... | equal _ = m --found your husband!
... | _       = zero --not married yet
getHusband woman ((m , w) ∷ couples) with compare woman w
... | equal _ = m --found your husband!
... | _       = getHusband woman couples --keep searching

getPreferenceList : ℕ → List (ℕ × List ℕ) → List ℕ
getPreferenceList person [] = [] --dummy case
getPreferenceList person ((p , preferences) ∷ ps) with compare person p
... | equal _ = preferences
... | _       = getPreferenceList person ps

{-# TERMINATING #-}
step : MatchingState → MatchingState

-- When there are no more free men, the matching is stable and this is the last step.
step (mkState [] engagedMen women couples) = mkState [] engagedMen women couples

-- Dummy case : the function shouldn't really be invoked with a man with empty preferences...
step (mkState ((n , []) ∷ freeMen) engagedMen women couples) = mkState ((n , []) ∷ freeMen) engagedMen women couples

-- Proposal step
step (mkState ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples) with getHusband w couples
... | (suc h)  with propose n (getHusband w couples) (getPreferenceList w women) --Woman has a husband, represented by his literal number
...             | true  = step (mkState freeMen ((n , prefs) ∷ engagedMen) women ((n , w) ∷ couples))
...             | false = step (mkState ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples)
-- Woman didn't have a husband yet (represented by zero) : must accept proposal
step (mkState ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples) | zero  = step (mkState freeMen ((n , prefs) ∷ engagedMen) women ((n , w) ∷ couples))

-- List of preferences of men and women from the Gale-Shapley canonical example
listMen : List (ℕ × List ℕ)
listMen = (1 , ( 1 ∷ 2 ∷ 3 ∷ [] )) ∷ (2 , ( 2 ∷ 3 ∷ 1 ∷ [])) ∷ (3 , ( 3 ∷ 1 ∷ 2 ∷ [])) ∷ []

listWomen : List (ℕ × List ℕ)
listWomen = (1 , ( 2 ∷ 3 ∷ 1 ∷ [] )) ∷ (2 , ( 3 ∷ 1 ∷ 2 ∷ [])) ∷ ((3 , ( 1 ∷ 2 ∷ 3 ∷ []))) ∷ []

