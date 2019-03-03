module GaleShapley where

open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Bool
open import Data.List
open import Relation.Nullary
open import Induction.WellFounded

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

-- Helper function to search for an element in a list of natural numbers.
positionInList : ℕ → List ℕ → ℕ → Maybe ℕ
positionInList x [] _ = nothing --searched everywhere but couldn't find it!
positionInList x (xs ∷ xss) zero with compare x xs
... | equal _  = just zero --found man at the tip of the list!
... | _        = positionInList x xss (suc zero) --accumulate and keep searching...
positionInList x (xs ∷ xss) (suc n) with compare x xs
... | equal _  = just (suc n) --found man somewhere in the list
... | _        = positionInList x xss (suc (suc n)) --accumulate and keep searching

-- m is the proposing man
-- h is the current husband of the woman
-- prefs is the preference list of the woman
-- returns true if the woman prefers m over h
propose : (m : ℕ)(h : ℕ)(prefs : List ℕ) → Bool
-- Woman compares
propose man h preferenceList with positionInList man preferenceList zero | positionInList h preferenceList zero
... | just p  | just q  = is-≤ p q --does she prefer the new guy to the current one?
... | just p  | nothing = false    --shouldn't happen in an ideal world : woman received a proposal from an unknown man??
... | nothing | just q  = false    --shouldn't happen in an ideal world : woman married an unknown man previously??
... | nothing | nothing = false    --shouldn't happen in an ideal world : who are these men??

-- We assume the "husbands" to be the proposing side,
-- therefore if women propose the pair looks like (wife, husband)
getHusband : ℕ → List (ℕ × ℕ) → Maybe ℕ
getHusband woman [] = nothing --not married yet and this is the first proposal in the algorithm!
getHusband woman ((m , w) ∷ []) with compare woman w
... | equal _ = just m --found your husband!
... | _       = nothing --not married yet
getHusband woman ((m , w) ∷ (c ∷ cs)) with compare woman w
... | equal _ = just m --found your husband!
... | _       = getHusband woman (c ∷ cs) --keep searching

-- Simply extract a preference list from the scheme of indexed lists.
getPreferenceList : ℕ → List (ℕ × List ℕ) → List ℕ
getPreferenceList person [] = [] --dummy case
getPreferenceList person ((p , preferences) ∷ ps) with compare person p
... | equal _ = preferences
... | _       = getPreferenceList person ps

-- Safely adding couples : previous marriages are unmade
safeAddNewCouple : (newCouple : ℕ × ℕ)(previousCouples : List (ℕ × ℕ)) → List (ℕ × ℕ)
safeAddNewCouple (m , w) [] = (m , w) ∷ []
safeAddNewCouple (m , w) ((a , b) ∷ []) with compare w b
... | equal _ = (m , w) ∷ []
... | _       = (m , w) ∷ (a , b) ∷ []
safeAddNewCouple (m , w) ((a , b) ∷ (c ∷ cs)) with compare w b
... | equal _ = (m , w) ∷ c ∷ cs
... | _       = (a , b) ∷ safeAddNewCouple (m , w) (c ∷ cs)

-- Safely adding new engaged men to the list : dumped man is removed
safeAddNewEngagedMan : (newEngagedMan : (ℕ × List ℕ))(prevFiance : ℕ)(prevEngagedMen : List (ℕ × List ℕ)) → List (ℕ × List ℕ)
safeAddNewEngagedMan (newFiance , prefs) prevFiance [] = (newFiance , prefs) ∷ []
safeAddNewEngagedMan (newFiance , prefs) prevFiance ((m , prefsM) ∷ []) with compare prevFiance m
... | equal _ = (newFiance , prefs) ∷ [] --kick him out!
... | _       = (newFiance , prefs) ∷ (m , prefsM) ∷ [] --safe to keep after all
safeAddNewEngagedMan (newFiance , prefs) prevFiance ((m , prefsM) ∷ ms ∷ engagedMen) with compare prevFiance m
... | equal _ = (newFiance , prefs) ∷ ms ∷ engagedMen --kick him out!
... | _       = (m , prefsM) ∷ safeAddNewEngagedMan (newFiance , prefs) prevFiance (ms ∷ engagedMen) --safe to keep... for now

step : MatchingState → MatchingState

-- When there are no more free men, the matching is stable and this is the last step.
step (mkState men [] engagedMen women couples) = mkState men [] engagedMen women couples

-- Dummy case : the function shouldn't really be invoked with a man with empty preferences.
-- But otherwise Agda would question the completeness of our pattern matching.
step (mkState men ((n , []) ∷ freeMen) engagedMen women couples) = mkState men ((n , []) ∷ freeMen) engagedMen women couples

-- Proposal step
step (mkState men ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples) with getHusband w couples
... | just h with propose n h (getPreferenceList w women) --Woman has a husband, represented by his literal number
...             | true  = mkState men ((h , getPreferenceList h engagedMen) ∷ freeMen) (safeAddNewEngagedMan (n , prefs) h engagedMen) women (safeAddNewCouple (n , w) couples)
...             | false = mkState men ((n , prefs) ∷ freeMen) engagedMen women couples
-- Woman didn't have a husband yet (represented by zero) : must accept proposal
step (mkState men ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples) | nothing  = mkState men freeMen ((n , prefs) ∷ engagedMen) women (safeAddNewCouple (n , w) couples)

sumPrefLists : (m : MatchingState) → ℕ
sumPrefLists (mkState men [] [] women couples) = 0
sumPrefLists (mkState men [] ((man , prefs) ∷ engagedMen) women couples) = length prefs + sumPrefLists (mkState men [] engagedMen women couples)
sumPrefLists (mkState men ((man , prefs) ∷ freeMen) engagedMen women couples) = length prefs + sumPrefLists (mkState men freeMen engagedMen women couples)

stepDec : (m : MatchingState) → sumPrefLists m > sumPrefLists (step m)
stepDec (mkState men [] engagedMen women couples) = {!!}
stepDec (mkState men (x ∷ freeMen) engagedMen women couples) = {!!}

{-# TERMINATING #-}
allSteps : (m : MatchingState)(k : ℕ) → sumPrefLists m ≡ k → MatchingState
allSteps m k p with step m
... | mkState men [] engagedMen women couples = mkState men [] engagedMen women couples
... | m' = allSteps m' (sumPrefLists m') refl

-- this is for correctness:
-- stepInv : (m : MatchingState) → Inv m → Inv (step m)

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

data _∈_ {A : Set}(a : A) : List A → Set where
  now   : (as : List A) → a ∈ (a ∷ as)
  later : {a' : A}{as : List A} → a ∈ as → a ∈ (a' ∷ as)

is-stable-matching' : MatchingState → Set
is-stable-matching' (mkState men freeMen engagedMen women couples) = (freeMen ≡ []) × ((c : ℕ × ℕ) → c ∈ couples → {!!} < {!!}) × {!!}

is-stable-matching : List (ℕ × List ℕ) → List (ℕ × List ℕ) → List (ℕ × ℕ) → Bool
-- Dummy cases
is-stable-matching [] women couples = false
is-stable-matching (m ∷ men) [] couples = false
is-stable-matching (m ∷ men) (w ∷ women) [] = false
-- Serious things!
is-stable-matching (m ∷ men) (w ∷ women) (c ∷ couples) = {!!}
