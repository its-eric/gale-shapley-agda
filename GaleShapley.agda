module GaleShapley where

open import Agda.Builtin.List
open import Agda.Builtin.String
open import Data.Maybe
open import Data.Nat
open import Data.Bool
open import Data.List

record Woman : Set
record Man : Set
record Couple : Set

record Woman where
  inductive
  field
    preferenceList : List Man
    id : ℕ
    husband : Maybe Man

open Woman

record Man where
  inductive
  field
    preferenceList : List Woman
    id : ℕ
    wife : Maybe Woman

open Man

data Pairable : Set where

record Couple where
  constructor _♥_
  inductive
  field
    partner₁ : Pairable
    partner₂ : Pairable

w : Woman
w = record
      { preferenceList = [] ; id = 0 ; husband = nothing }

m : Man
m = record
      { preferenceList =  [] ; id = 0 ; wife = nothing }

lw : List Woman
lw = preferenceList m

lm : List Man
lm = preferenceList w

someId : ℕ
someId = id w

acceptsToMarry : Woman →  Man →  Bool
acceptsToMarry woman man = true

-- Take the next woman from the list and propose to her, returning the updated list
_canMarry_ : ∀ {a b} {A : Set a} {B : Set b} →  A →  B →  Bool
a canMarry b = true

proposeNext : ∀ {a} {A : Set a} →  A -> A
proposeNext m = m
-- proposeNext m = record m { preferenceList = propose (preferenceList m) ; wife = nothing }

nextToPropose : ∀ {a} {A : Set a} →  List A → Maybe A
nextToPropose [] = nothing
nextToPropose (x ∷ list) = just x

marry : ∀ {a b} {A : Set a} {B : Set b} →  Pairable →  Pairable → Couple
marry a b = a ♥  b

analyzeProposal : List Man → List Woman → List Couple
analyzeProposal = {!!}

stableMatching : List Man → List Woman →  Maybe (List Couple)
stableMatching [] bs = nothing
stableMatching as [] = nothing
stableMatching as bs = nothing
