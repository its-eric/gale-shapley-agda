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

step : MatchingState → MatchingState
-- When there are no more free men, the matching is stable and this is the last step.
step (mkState [] engagedMen women couples) = mkState [] engagedMen women couples
-- Dummy case : the function shouldn't really be invoked with a man with empty preferences...
step (mkState ((n , []) ∷ freeMen) engagedMen women couples) = mkState ((n , []) ∷ freeMen) engagedMen women couples
step (mkState ((n , x ∷ prefs) ∷ freeMen) engagedMen women couples) with propose n (getHusband x couples) (getPreferenceList x women)
... | true  = mkState freeMen ((n , prefs) ∷ engagedMen) women ((n , x) ∷ couples)
... | false = mkState ((n , x ∷ prefs) ∷ freeMen) engagedMen women couples

-- step record { freemen = [] ; engamen = engamen ; women = women ; couples = couples } = record { freemen = [] ; engamen = engamen ; women = women ; couples = couples }
-- step record { freemen = (x ∷ freemen) ; engamen = engamen ; women = women ; couples = couples } = {!!}


{-
updateFiancee : Man -> Woman → Man
updateFiancee m w = record m { fiancee = just w }

updateFiance : Woman → Man → Woman
updateFiance w m = record w { fiance = just m }

-}

{-
nextWoman : List  → Man → Maybe Couple
propose candidates man with bestWoman man
propose candidates man | just woman with woman acceptsToMarry man
...                    | true  = just (marry man woman)
...                    | false = nothing
propose candidates man | nothing = nothing

  where
    womanToPropose = head (Man.preferenceList man)

    listMen : Maybe Woman → List Man
    listMen (just womanToPropose) = Woman.preferenceList womanToPropose
    listMen nothing = []
    
    changeState : MatchingState → MatchingState
    changeState candidates = candidates

zipCouples : List Man → List Couple
zipCouples [] = []
zipCouples (m ∷ men) with fiancee m
... | just woman = marry m woman ∷ zipCouples men
... | nothing    = zipCouples men
-}

{- TODO : Update free men... Decide how to do this -}

{-
-- TODO Delete guys

takeWoman : List ℕ → List ℕ
takeWoman _ = _

getElem : ℕ → List (List ℕ) → List ℕ
getElem _ [] = []
getElem 0 (x ∷ xs) = x
getElem (suc n) (x ∷ xs) = {!!}

isManSingle : ℕ → List (ℕ × ℕ) → Bool
isManSingle n [] = true
isManSingle n (c ∷ couples) with (proj₁ c) ≡ n
... | false = isManSingle n couples
... | true  = false

getNextFreeMan : List (ℕ × ℕ) → ℕ → Maybe ℕ
getNextFreeMan [] n = just zero
getNextFreeMan couples zero = just zero
getNextFreeMan couples (suc n) with isManSingle (suc n) couples
... | true  = just (suc n)
... | false = getNextFreeMan couples n

step : MatchingState → MatchingState
step ms with getNextFreeMan (couples ms) (length (men ms))
... | just man = ms -- Split up another case expression for the proposal
... | nothing  = ms -- Matching is stable
-}
