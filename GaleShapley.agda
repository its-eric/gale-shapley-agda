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
... | Dec.yes _ = Bool.true
... | Dec.no _ = Bool.false

acceptsToMarry : Woman →  Man →  Bool
acceptsToMarry woman man with fiance woman
... | just fiance = is-≤ (elemIndex man (preferenceList woman)) (elemIndex fiance (preferenceList woman))

-- Take the next woman from the list and propose to her, returning the updated list
_canMarry_ : ∀ {a b} {A : Set a} {B : Set b} →  A →  B →  Bool
a canMarry b = true

proposeNext : ∀ {a} {A : Set a} →  A -> A
proposeNext m = m
-- proposeNext m = record m { preferenceList = propose (preferenceList m) ; wife = nothing }

nextToPropose : ∀ {a} {A : Set a} →  List A → Maybe A
nextToPropose [] = nothing
nextToPropose (x ∷ list) = just x

marry : ∀ {a b} {A : Set a} {B : Set b} →  Man → Woman → Couple
marry man woman = man ♥ woman

areMarriagesStable : List Couple → Bool
areMarriagesStable cs = ?

propose : MatchingState → Man → Maybe Couple
propose candidates man =
  let
    womanToPropose = head (preferenceList man)
    listMen = just (Woman.preferenceList womanToPropose)

    changeState : MatchingState → MatchingState
    changeState candidates = candidates
  in 
     (just womanToPropose) acceptsToMarry man
    {- TODO Rewrite this chunk
    with womanToPropose acceptsToMarry man
    ... | candidates -}

zipCouples : List Man → List Woman → List Couple
zipCouples men women = []

makeNextProposal : MatchingState → List Couple
makeNextProposal candidates = foldl propose candidates (head MatchingState.freeMen candidates)

makeNextProposal candidates with propose (head MatchingState.freeMen candidates)
makeNextProposal men women | nothing = makeNextProposal men women
makeNextProposal men women | just couple with areMarriagesStable (zipCouples men women)
makeNextProposal men women | just couple | true  = zipCouples men women
makeNextProposal men women | just couple | false = makeNextProposal men women

-- TODO Delete guys

stableMatching : List Man → List Woman → List Couple
stableMatching [] bs = []
stableMatching as [] = []
stableMatching as bs = dropWhile (not null MatchingState.freeMen candidates) (makeNextProposal candidates)
  where
  candidates : MatchingState
  candidates = record
      { freeMen = as ; men = as ; women = bs }
