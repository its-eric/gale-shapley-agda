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
    men : List (ℕ × List ℕ)
    freeMen : List (ℕ × List ℕ)
    engagedMen : List (ℕ × List ℕ)
    women : List (ℕ × List ℕ)
    couples : List (ℕ × ℕ)

-- Code by @yeputons on Stack Overflow :D
is-≤ : ℕ → ℕ → Bool
is-≤ a b with a ≤? b
... | Dec.yes _ = true
... | Dec.no _ = false

positionInList : ℕ → List ℕ → ℕ → ℕ
positionInList x [] _ = zero --when there is no list...?
positionInList x (xs ∷ xss) zero with compare x xs
... | equal _  = zero --found man at the tip of the list!
... | _        = positionInList x xss (suc zero) --accumulate and keep searching...
positionInList x (xs ∷ xss) (suc n) with compare x xs
... | equal _  = suc n --found man somewhere in the list
... | _        = positionInList x xss (suc (suc n)) --accumulate and keep searching

propose : ℕ → ℕ → List ℕ → Bool
-- If the woman is married to 0, she is single. This call won't happen in the current implementation.
propose man zero preferenceList = false
-- Otherwise she must compare
propose man (suc n) preferenceList = is-≤ (positionInList man preferenceList zero) (positionInList (suc n) preferenceList zero)

-- We assume the "husbands" to be the proposing side,
-- therefore if women propose the pair looks like (wife, husband)
getHusband : ℕ → List (ℕ × ℕ) → ℕ
getHusband woman [] = zero --not married yet and this is the first proposal in the algorithm!
getHusband woman ((m , w) ∷ []) with compare woman w
... | equal _ = m --found your husband!
... | _       = zero --not married yet
getHusband woman ((m , w) ∷ (c ∷ cs)) with compare woman w
... | equal _ = m --found your husband!
... | _       = getHusband woman (c ∷ cs) --keep searching

getPreferenceList : ℕ → List (ℕ × List ℕ) → List ℕ
getPreferenceList person [] = [] --dummy case
getPreferenceList person ((p , preferences) ∷ ps) with compare person p
... | equal _ = preferences
... | _       = getPreferenceList person ps

-- Safely adding couples : previous marriages are unmade
addNewCouple : (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
addNewCouple (m , w) [] = (m , w) ∷ []
addNewCouple (m , w) ((a , b) ∷ []) with compare w b
... | equal _ = (m , w) ∷ []
... | _       = (m , w) ∷ (a , b) ∷ []
addNewCouple (m , w) ((a , b) ∷ (c ∷ cs)) with compare w b
... | equal _ = (m , w) ∷ c ∷ cs
... | _       = (a , b) ∷ addNewCouple (m , w) (c ∷ cs)

-- Safely adding new engaged men to the list : dumped man is removed
addNewEngagedMan : (ℕ × List ℕ) → ℕ → List (ℕ × List ℕ) → List (ℕ × List ℕ)
addNewEngagedMan (newFiance , prefs) prevFiance [] = (newFiance , prefs) ∷ []
addNewEngagedMan (newFiance , prefs) prevFiance ((m , prefsM) ∷ []) with compare prevFiance m
... | equal _ = (newFiance , prefs) ∷ [] --kick him out!
... | _       = (newFiance , prefs) ∷ (m , prefsM) ∷ [] --safe to keep after all
addNewEngagedMan (newFiance , prefs) prevFiance ((m , prefsM) ∷ ms ∷ engagedMen) with compare prevFiance m
... | equal _ = (newFiance , prefs) ∷ ms ∷ engagedMen --kick him out!
... | _       = (m , prefsM) ∷ addNewEngagedMan (newFiance , prefs) prevFiance (ms ∷ engagedMen) --safe to keep... for now

-- addNewEngagedMan newFiance prevFiance ((m , prefsM) ∷ engagedMen) = newFiance ∷ filter (λ m → compare prevFiance m) engagedMen

{-# TERMINATING #-}
step : MatchingState → MatchingState

-- When there are no more free men, the matching is stable and this is the last step.
step (mkState men [] engagedMen women couples) = mkState men [] engagedMen women couples

-- Dummy case : the function shouldn't really be invoked with a man with empty preferences...
step (mkState men ((n , []) ∷ freeMen) engagedMen women couples) = mkState men ((n , []) ∷ freeMen) engagedMen women couples

-- Proposal step
step (mkState men ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples) with getHusband w couples
... | (suc h)  with propose n (suc h) (getPreferenceList w women) --Woman has a husband, represented by his literal number
...             | true  = step (mkState men (((suc h) , getPreferenceList (suc h) engagedMen) ∷ freeMen) (addNewEngagedMan (n , prefs) (suc h) engagedMen) women (addNewCouple (n , w) couples))
...             | false = step (mkState men ((n , prefs) ∷ freeMen) engagedMen women couples)
-- Woman didn't have a husband yet (represented by zero) : must accept proposal
step (mkState men ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples) | zero  = step (mkState men freeMen ((n , prefs) ∷ engagedMen) women (addNewCouple (n , w) couples))

-- List of preferences of men and women from the Gale-Shapley canonical example
listMen : List (ℕ × List ℕ)
listMen = (1 , ( 1 ∷ 2 ∷ 3 ∷ [] )) ∷ (2 , ( 2 ∷ 3 ∷ 1 ∷ [])) ∷ (3 , ( 3 ∷ 1 ∷ 2 ∷ [])) ∷ []

listWomen : List (ℕ × List ℕ)
listWomen = (1 , ( 2 ∷ 3 ∷ 1 ∷ [] )) ∷ (2 , ( 3 ∷ 1 ∷ 2 ∷ [])) ∷ ((3 , ( 1 ∷ 2 ∷ 3 ∷ []))) ∷ []

-- Extra example : men and women have only one possible stable set of marriages! What could happen...?

listDifficultMen : List (ℕ × List ℕ)
listDifficultMen = (1 , ( 1 ∷ 2 ∷ 3 ∷ 4 ∷ [] )) ∷ (2 , ( 1 ∷ 4 ∷ 3 ∷ 2 ∷ [] )) ∷ (3 , ( 2 ∷ 1 ∷ 3 ∷ 4 ∷ [])) ∷ ((4 , ( 4 ∷ 2 ∷ 3 ∷ 1 ∷ []))) ∷ []

listDifficultWomen : List (ℕ × List ℕ)
listDifficultWomen = (1 , ( 4 ∷ 3 ∷ 1 ∷ 2 ∷ []) ) ∷ (2 , ( 2 ∷ 4 ∷ 1 ∷ 3 ∷ [])) ∷ (3 , ( 4 ∷ 1 ∷ 2 ∷ 3 ∷ [])) ∷ (4 , (3 ∷ 2 ∷ 1 ∷ 4 ∷ [])) ∷ []

-- Proofs! :D

is-stable-matching : List (ℕ × List ℕ) → List (ℕ × List ℕ) → List (ℕ × ℕ) → Bool
is-stable-matching = {!!}
