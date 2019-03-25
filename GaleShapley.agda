module GaleShapley where

open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Data.Empty
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Bool
open import Data.List
open import Data.Sum
open import Relation.Nullary
open import Induction.WellFounded
open import Relation.Binary.PropositionalEquality

infix 3 _>just_
infix 4 _from>_

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
positionInListHelper : ℕ → List ℕ → ℕ → Maybe ℕ
positionInListHelper x [] _ = nothing --searched everywhere but couldn't find it!
positionInListHelper x (xs ∷ xss) zero with compare x xs
... | equal _  = just zero --found man at the tip of the list!
... | _        = positionInListHelper x xss (suc zero) --accumulate and keep searching...
positionInListHelper x (xs ∷ xss) (suc n) with compare x xs
... | equal _  = just (suc n) --found man somewhere in the list
... | _        = positionInListHelper x xss (suc (suc n)) --accumulate and keep searching

positionInList : ℕ → List ℕ → Maybe ℕ
positionInList n ns = positionInListHelper n ns zero

-- m is the proposing man
-- h is the current husband of the woman
-- prefs is the preference list of the woman
-- returns true if the woman prefers m over h
propose : (m : ℕ)(h : ℕ)(prefs : List ℕ) → Bool
-- Woman compares
propose man h preferenceList with positionInList man preferenceList | positionInList h preferenceList
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

getWife : ℕ → List (ℕ × ℕ) → Maybe ℕ
getWife man [] = nothing
getWife man ((m , w) ∷ []) with compare man m
... | equal _ = just w --found your wife!
... | _       = nothing --not married yet
getWife man ((m , w) ∷ (c ∷ cs)) with compare man m
... | equal _ = just w --found your wife!
... | _       = getHusband man (c ∷ cs) --keep searching

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
sumPrefLists (mkState men [] ((man , []) ∷ engagedMen) women couples) = 0 + sumPrefLists (mkState men [] engagedMen women couples)
sumPrefLists (mkState men [] ((man , p ∷ prefs) ∷ engagedMen) women couples) = length (p ∷ prefs) + sumPrefLists (mkState men [] engagedMen women couples)
sumPrefLists (mkState men ((man , []) ∷ freeMen) [] women couples) = 0 + sumPrefLists (mkState men freeMen [] women couples)
sumPrefLists (mkState men ((man , p ∷ prefs) ∷ freeMen) [] women couples) = length (p ∷ prefs) + sumPrefLists (mkState men freeMen [] women couples)
sumPrefLists (mkState men ((man₁ , []) ∷ freeMen) ((man₂ , []) ∷ engagedMen) women couples) = 0 + sumPrefLists (mkState men freeMen engagedMen women couples)
sumPrefLists (mkState men ((man₁ , []) ∷ freeMen) ((man₂ , p₂ ∷ prefs₂) ∷ engagedMen) women couples) = 0 + length (p₂ ∷ prefs₂) + sumPrefLists (mkState men freeMen engagedMen women couples)
sumPrefLists (mkState men ((man₁ , p₁ ∷ prefs₁) ∷ freeMen) ((man₂ , []) ∷ engagedMen) women couples) = length (p₁ ∷ prefs₁) + 0 + sumPrefLists (mkState men freeMen engagedMen women couples)
sumPrefLists (mkState men ((man₁ , p₁ ∷ prefs₁) ∷ freeMen) ((man₂ , p₂ ∷ prefs₂) ∷ engagedMen) women couples) = length (p₁ ∷ prefs₁) + length (p₂ ∷ prefs₂) + sumPrefLists (mkState men freeMen engagedMen women couples)

-- cong : (f : A → B) → a ≡ a' → f a ≡ f a'
sumPrefLemma : ∀ men freeMen engagedMen women couples men' women' couples' → 
  sumPrefLists (mkState men freeMen engagedMen women couples) ≡ sumPrefLists (mkState men' freeMen engagedMen women' couples')
sumPrefLemma men [] [] women couples men' women' couples' = refl
sumPrefLemma men [] ((man , []) ∷ engagedMen) women couples men' women' couples' = {!!}
sumPrefLemma men [] ((man , p ∷ prefs) ∷ engagedMen) women couples men' women' couples' = {!!}
sumPrefLemma men ((man , []) ∷ freeMen) [] women couples men' women' couples' = {!!}
sumPrefLemma men ((man , p ∷ prefs) ∷ freeMen) [] women couples men' women' couples' = {!!}
sumPrefLemma men ((man₁ , []) ∷ freeMen) ((man₂ , []) ∷ engagedMen) women couples men' women' couples' = {!!}
sumPrefLemma men ((man₁ , []) ∷ freeMen) ((man₂ , p₂ ∷ prefs₂) ∷ engagedMen) women couples men' women' couples' = {!!}
sumPrefLemma men ((man₁ , p₁ ∷ prefs₁) ∷ freeMen) ((man₂ , []) ∷ engagedMen) women couples men' women' couples' = {!!}
sumPrefLemma men ((man₁ , p₁ ∷ prefs₁) ∷ freeMen) ((man₂ , p₂ ∷ prefs₂) ∷ engagedMen) women couples men' women' couples' = {!!}

{--
sumPrefLemma men [] ((man , prefs) ∷ engagedMen) women couples men' women' couples' = sumPrefLemma men [] engagedMen women couples men' women' couples' -- (length prefs +_) (sumPrefLemma men [] engagedMen women couples men' women' couples')
sumPrefLemma men ((man , prefs) ∷ freeMen) [] women couples men' women' couples' = {!!} --cong (length prefs +_) (sumPrefLemma men freeMen [] women couples men' women' couples')
sumPrefLemma men ((man₁ , prefs₁) ∷ freeMen) ((man₂ , prefs₂) ∷ engagedMen) women couples men' women' couples' = {!!} --cong (length prefs₁ + length prefs₂ +_) (sumPrefLemma men freeMen engagedMen women couples men' women' couples')
-}

decompLemma : ∀ men freeMen engagedMen (prefs : List ℕ) women couples → ¬ (freeMen ≡ []) → ¬ (engagedMen ≡ []) → ¬ (prefs ≡ []) →
  length prefs + sumPrefLists (mkState men freeMen engagedMen women couples) ≥ sumPrefLists (step (mkState men freeMen engagedMen women couples))
decompLemma men [] [] [] women couples p₁ p₂ p₃ = z≤n
decompLemma men [] [] (p ∷ prefs) women couples p₁ p₂ p₃ = ⊥-elim (p₁ refl)
decompLemma men [] (man ∷ engagedMen) [] women couples p₁ p₂ p₃ = ≤-refl
decompLemma men [] (man ∷ engagedMen) (x₁ ∷ prefs) women couples p₁ p₂ p₃ = ⊥-elim (p₁ refl)
decompLemma men (man ∷ freeMen) [] [] women couples p₁ p₂ p₃ =  ⊥-elim (p₂ refl)
decompLemma men (man ∷ freeMen) [] (p ∷ prefs) women couples p₁ p₂ p₃ = ⊥-elim (p₂ refl)
decompLemma men (man₁ ∷ freeMen) (man₂ ∷ engagedMen) [] women couples p₁ p₂ p₃ = ⊥-elim (p₃ refl)
decompLemma men (man₁ ∷ freeMen) (man₂ ∷ engagedMen) (p ∷ prefs) women couples p₁ p₂ p₃ = {!!}

stepDec : (m : MatchingState) → sumPrefLists m ≥ sumPrefLists (step m)
stepDec (mkState men [] [] women couples) = z≤n
stepDec (mkState men [] ((man , prefs) ∷ engagedMen) women couples) = ≤-refl
stepDec (mkState men ((man , w ∷ prefs) ∷ freeMen) engagedMen women couples) with getHusband w couples
...             | just h with propose man h (getPreferenceList w women)
...             | true = {!!}
...             | false = {!!} -- n≤1+n _
stepDec (mkState men ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples) | nothing = {!!}

{--
stepDec (mkState men []             engagedMen women couples) = {!!} -- z≤n
stepDec (mkState men ((n , []) ∷ freeMen) engagedMen women couples) = ≤-refl
stepDec (mkState men ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples) with getHusband w couples
...             | just h with propose n h (getPreferenceList w women)
...             | true = {!!}
...             | false = {!!} -- n≤1+n _
stepDec (mkState men ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples) | nothing = {!!}
-}

{-# TERMINATING #-}
allSteps : (m : MatchingState)(k : ℕ) → sumPrefLists m ≡ k → MatchingState
allSteps m k p with step m
... | mkState men [] engagedMen women couples = mkState men [] engagedMen women couples
... | m' = allSteps m' (sumPrefLists m') refl

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

-- The type of elements that belong to a list.
data _∈_ {A : Set}(a : A) : List A → Set where
  now   : (as : List A) → a ∈ (a ∷ as)
  later : {a' : A}{as : List A} → a ∈ as → a ∈ (a' ∷ as)

-- Bigger than comparison for Maybe ℕ-typed elements. 
data _>just_ : Maybe ℕ → Maybe ℕ → Set where
  _from>_ : {m n : ℕ} → m > n → just m >just just n

-- Helper for the condition of stability: a person is better than another one
-- in a preference list if it appears earlier in it.
_≻[_]_ : ℕ → List ℕ → Maybe ℕ → Set
person ≻[ list ] just person₂ = positionInList person₂ list >just positionInList person list
person ≻[ list ] nothing = ⊥

-- Given a man and a woman and their preferences, the condition of stability is satisfied if
-- another m' and w' are better positioned in their preference lists than each other AT THE SAME TIME.
conditionOfStabilitySatisfied : (man : ℕ × List ℕ)(woman : ℕ × List ℕ)(m' w' : Maybe ℕ) → Set
conditionOfStabilitySatisfied (man , prefsM) (woman , prefsW) m' w' = ¬ ( ( woman ≻[ prefsM ] w' ) × ( man ≻[ prefsW ] m' ))

-- A matching is stable if the condition of stability is satisfied for every pair of man and woman not married.
is-stable-matching : MatchingState → Set
is-stable-matching (mkState men freeMen engagedMen women couples) =
  (freeMen ≡ []) × (
      (m w : ℕ)(m' w' : Maybe ℕ) → ¬ ((m , w) ∈ couples) → ¬ (getHusband w couples ≡ nothing) → ¬ (getWife m couples ≡ nothing) →
        (m' ≡ getHusband w couples) → (w' ≡ getWife m couples) →
          conditionOfStabilitySatisfied (m , getPreferenceList m men) (w , getPreferenceList w women) m' w')
  
exStart exEnd exEndExpected : MatchingState
exStart       = mkState listMen listMen [] listWomen []
-- Gale and Shapley tell us that, for the first simple example, each men gets his first woman from the list as a wife
-- and there are no conflicts among them. So we expect the following end state:
exEndExpected = mkState listMen [] ((3 , (1 ∷ 2 ∷ [])) ∷ ((2 , 3 ∷ 1 ∷ []) ∷ (1 , 2 ∷ 3 ∷ []) ∷ [] )) listWomen ((2 , 2) ∷ (3 , 3) ∷ (1 , 1) ∷ [])
exEnd         = step (step (step (step exStart)))

resultIsWhatWeExpected : exEnd ≡ exEndExpected
resultIsWhatWeExpected = refl

ex2Start ex2End ex2EndExpected : MatchingState
ex2Start         = mkState listDifficultMen listDifficultMen [] listDifficultWomen []
-- A second, harder example is given where there is only one possible stable set of marriages.
ex2EndExpected   = mkState listDifficultMen [] ((1 , ( 4 ∷ [] )) ∷ (4 , (3 ∷ 1 ∷ [])) ∷ (2 , ( 3 ∷ 2 ∷ [] )) ∷ (3 , ( 3 ∷ 4 ∷ [])) ∷ []) listDifficultWomen (((2 , 4) ∷ (4 , 2) ∷ (1 , 3) ∷ (3 , 1) ∷ []))
ex2End           = step (step (step (step (step (step (step (step (step ex2Start))))))))

result2IsWhatWeExpected : ex2End ≡ ex2EndExpected
result2IsWhatWeExpected = refl

{--
matchIsStableHelper :  (m w : ℕ)(prefsM prefsW : List ℕ) →
      ¬ ((m , w) ∈ MatchingState.couples exEnd) →
      conditionOfStabilitySatisfied
      (m ,
       (getPreferenceList m
        (MatchingState.men exEnd)))
      (w ,
       (getPreferenceList w
        (MatchingState.women exEnd)))
      (MatchingState.couples exEnd)
matchIsStableHelper m w prefsM prefsW p = {!!}

matchIsStableHelper _ _ p (now .((3 , 3) ∷ (1 , 1) ∷ [])) (now .((3 , 3) ∷ (1 , 1) ∷ [])) = ⊥-elim (p refl)
matchIsStableHelper _ _ p (now .((3 , 3) ∷ (1 , 1) ∷ [])) (later (now .((1 , 1) ∷ []))) = {!!} , {!!}
matchIsStableHelper _ _ p (now .((3 , 3) ∷ (1 , 1) ∷ [])) (later (later (now .[]))) = {!!}
matchIsStableHelper _ _ p (now .((3 , 3) ∷ (1 , 1) ∷ [])) (later (later (later ())))
matchIsStableHelper _ _ p (later (now .((1 , 1) ∷ []))) (now .((3 , 3) ∷ (1 , 1) ∷ [])) = {!!}
matchIsStableHelper _ _ p (later (later (now .[]))) (now .((3 , 3) ∷ (1 , 1) ∷ [])) = {!!}
matchIsStableHelper _ _ p (later (later (later ()))) (now .((3 , 3) ∷ (1 , 1) ∷ []))
matchIsStableHelper _ _ p (later (now .((1 , 1) ∷ []))) (later (now .((1 , 1) ∷ []))) = ⊥-elim (p refl)
matchIsStableHelper _ _ p (later (now .((1 , 1) ∷ []))) (later (later (now .[]))) = {!!}
matchIsStableHelper _ _ p (later (now .((1 , 1) ∷ []))) (later (later (later ())))
matchIsStableHelper _ _ p (later (later (now .[]))) (later (now .((1 , 1) ∷ []))) = {!!}
matchIsStableHelper _ _ p (later (later (later ()))) (later (now .((1 , 1) ∷ [])))
matchIsStableHelper _ _ p (later (later (now .[]))) (later (later (now .[]))) = ⊥-elim (p refl)
matchIsStableHelper _ _ p (later (later (now .[]))) (later (later (later ())))
matchIsStableHelper _ _ p (later (later (later ()))) (later (later (now .[])))
matchIsStableHelper _ _ p (later (later (later ()))) (later (later (later p₂)))
-}

matchIsStable : is-stable-matching exEnd
matchIsStable = refl , {!!} --matchIsStableHelper

-- In order to define that a matching m₁ is better than a matching m₂,
-- we take into consideration that every man gets a better (earlier in his list) wife
-- in m₁ than in m₂; this can be seen from the size of his preference list in the final
-- state of the matching. 
is-better-matching : (m₁ m₂ : MatchingState) → Set
is-better-matching (mkState men freeMen engagedMen women couples) (mkState men₁ freeMen₁ engagedMen₁ women₁ couples₁) =
  is-stable-matching (mkState men freeMen engagedMen women couples) × is-stable-matching (mkState men₁ freeMen₁ engagedMen₁ women₁ couples₁) ×
   ((m₁ m₂ : ℕ × List ℕ) → m₁ ∈ engagedMen →  m₂ ∈ engagedMen₁ → proj₁ m₁ ≡ proj₁ m₂ → length (proj₂ m₁) ≤ length (proj₂ m₂))

-- Let us demonstrate with the first canonical example. Gale and Shapley tell us
-- that another possible stable marriage (not return by their algorithm) is obtained
-- by giving every woman her first choice:
anotherPossibleStableMatching : MatchingState
anotherPossibleStableMatching = mkState listMen [] _ listWomen ((3 , 1) ∷ (1 , 2) ∷ (2 , 3) ∷ [])

matchIsBetter : is-better-matching exEnd anotherPossibleStableMatching
matchIsBetter = {!!}


{-- this is for correctness:
-- stepInv : (m : MatchingState) → Inv m → Inv (step m)

Something like:

data GaleShapleyInv : (m : MatchingState) → Set where
  inv : m ∈ m.listMen → w ∈ m.listWomen → b ∉ l(a) → (∃ a′ ∈ m : a′ ≻_{b} a ∨ p(a) = b
-}
