module GaleShapley where

open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Bool
open import Data.List
open import Relation.Nullary using (Dec)

record MatchingState : Set where
  field
    men : List (List ℕ)
    women : List (List ℕ)
    couples : List (ℕ × ℕ)

open MatchingState

-- Code by @yeputons on Stack Overflow :D
is-≤ : ℕ → ℕ → Bool
is-≤ a b with a ≤? b
... | Dec.yes _ = true
... | Dec.no _ = false

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

-- TODO Delete guys

propose : List ℕ → ℕ → Bool
propose _ _ = false

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
