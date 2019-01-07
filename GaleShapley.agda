module GaleShapley where

open import Agda.Builtin.List
open import Agda.Builtin.String
open import Data.Maybe
open import Data.Nat
open import Data.Bool
open import Data.List
open import Relation.Nullary using (Dec)

record Man : Set

record Woman : Set where
  inductive
  field
    preferenceList : List Man
    id : ℕ
    fiance : Maybe Man

open Woman

record Man where
  inductive
  field
    preferenceList : List Woman
    id : ℕ
    fiancee : Maybe Woman

open Man

record Couple : Set where
  constructor _♥_
  inductive
  field
    husband : Man
    wife : Woman

record MatchingState : Set where
  field
    freeMen : List Man
    men : List Man
    women : List Woman

open MatchingState

w : Woman
w = record
      { preferenceList = [] ; id = 0 ; fiance = nothing }

m : Man
m = record
      { preferenceList =  [] ; id = 0 ; fiancee = nothing }

lw : List Woman
lw = preferenceList m

lm : List Man
lm = preferenceList w

someId : ℕ
someId = id w

elemIndex : ∀ {a} {A : Set a} → A → List A → ℕ
elemIndex elem xs = ?

-- Code by @yeputons on Stack Overflow :D
is-≤ : ℕ → ℕ → Bool
is-≤ a b with a ≤? b
... | Dec.yes _ = true
... | Dec.no _ = false

updateFiancee : Man -> Woman → Man
updateFiancee m w = record m { fiancee = just w }

updateFiance : Woman → Man → Woman
updateFiance w m = record w { fiance = just m }

marry : Man → Woman → Couple
marry man woman = (updateFiancee man woman) ♥ (updateFiance woman man)

_acceptsToMarry_ : Woman →  Man → Bool
woman acceptsToMarry man with fiance woman
... | just fiance = is-≤ (elemIndex fiance (preferenceList woman)) (elemIndex man (preferenceList woman))
... | nothing = true

areMarriagesStable : List Couple → Bool
areMarriagesStable cs = false

bestWoman : Man → Maybe Woman
bestWoman m = head (preferenceList m)


propose : MatchingState → Man → Maybe Couple
propose candidates man with bestWoman man
propose candidates man | just woman with woman acceptsToMarry man
...                    | true  = just (marry man woman)
...                    | false = nothing
propose candidates man | nothing = nothing

{-
  where
    womanToPropose = head (Man.preferenceList man)

    listMen : Maybe Woman → List Man
    listMen (just womanToPropose) = Woman.preferenceList womanToPropose
    listMen nothing = []
    
    changeState : MatchingState → MatchingState
    changeState candidates = candidates
-}

zipCouples : List Man → List Couple
zipCouples [] = []
zipCouples (m ∷ men) with fiancee m
... | just woman = marry m woman ∷ zipCouples men
... | nothing    = zipCouples men

{- TODO : Update free men... Decide how to do this -}

makeNextProposal : MatchingState → List Couple
makeNextProposal candidates with propose candidates (just (head (MatchingState.freeMen candidates)))
makeNextProposal candidates | nothing = makeNextProposal candidates
makeNextProposal candidates | just couple with areMarriagesStable (zipCouples men women)
makeNextProposal candidates | just couple | true  = zipCouples men women
-- Think about this
makeNextProposal candidates | just couple | false = makeNextProposal (record candidates { })

-- TODO Delete guys

stableMatching : List Man → List Woman → List Couple
stableMatching [] bs = []
stableMatching as [] = []
stableMatching as bs = dropWhile (not null MatchingState.freeMen candidates) (makeNextProposal candidates)
  where
  candidates : MatchingState
  candidates = record
      { freeMen = as ; men = as ; women = bs }
