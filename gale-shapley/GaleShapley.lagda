\newcommand{\GaleShapley}{%

To define the Gale-Shapley algorithm in Agda, we need a data structure which captures the state of the procedure in its various elements, in order to reason about its properties in an expressive enough manner that proofs can be written in the same manner as we have reasoned logically about the properties of the algorithm in chapter \ref{Chapter3}. We make use here of Agda's record types.

In Agda syntax, a $record$ defines a type that groups some values, in our case, the details of the group of men and women and their preference lists for the "matching ritual". Men are preference lists indexed over a representative natural number as well as women, giving a similar "state space" to the problem as the one defined in the previous mathematical specification. This type can be constructed with the $mkState$ keyword, and its elements are accessible at all times through (pattern matching and) projection functions defined automatically by Agda.

Two extra functions are also defined, $lengthPrefs$ and $compSumPrefLists$ which help us calculate the length of the preference lists of men in a matching state:

\begin{code}[hide]

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
\end{code}

\begin{code}
lengthPrefs : List (ℕ × List ℕ) → ℕ
lengthPrefs [] = 0
lengthPrefs ((_ , l) ∷ xs) = length l + lengthPrefs xs

compSumPrefLists : (freeMen engagedMen : List (ℕ × List ℕ) ) → ℕ
compSumPrefLists freeMen engagedMen = lengthPrefs freeMen + lengthPrefs engagedMen

record MatchingState : Set where
  constructor mkState
  field
    men : List (ℕ × List ℕ)
    freeMen : List (ℕ × List ℕ)
    engagedMen : List (ℕ × List ℕ)
    women : List (ℕ × List ℕ)
    couples : List (ℕ × ℕ)
    sumPrefLists : ℕ
    sumEq : sumPrefLists ≡ lengthPrefs freeMen + lengthPrefs engagedMen

\end{code}

We expect to start the execution of the algorithm with a copy of all men in the $freeMen$ list, and finish with all of them in $engagedMen$. A list of couples can then be extracted from $couples$. The lists $men$ and $women$ are preserved throughout the execution; the reason behind this particular design decision is to facilitate the writing of predicates in Agda, since, as introduced before, proofs involving the Gale-Shapley algorithm may discuss at the same time the "absolute" preference list of men and women or the \emph{current state} of their preference lists at a certain step of the algorithm. Therefore the current state of a certain man's preference list can be observed either in this or that list given that the man is free or engaged at a certain point during the execution.

We give two extra implementation-specific components: we keep track of the sum of preference lists of men, and at all times provide a proof that this number is in fact equal to the sum if it is computed.

Some helper functions are defined as tools to support the algorithm. They are defined always over pattern matching, typed with the help of Agda's case expansions. Very similar code can be written, for example, in Haskell to perform these operations over lists:

\begin{code}
-- Code by @yeputons on Stack Overflow :D
is-≤ : ℕ → ℕ → Bool
is-≤ a b with a ≤′? b
... | Dec.yes _ = true
... | Dec.no _ = false

-- Helper function to search for an element in a list of natural numbers.
positionInListHelper : ℕ → List ℕ → ℕ → Maybe ℕ
--searched everywhere but couldn't find it!
positionInListHelper x [] _ = nothing

positionInListHelper x (xs ∷ xss) zero with compare x xs
--found man at the tip of the list!
... | equal _  = just zero
 --accumulate and keep searching...
... | _        = positionInListHelper x xss (suc zero)
positionInListHelper x (xs ∷ xss) (suc n) with compare x xs
--found man somewhere in the list
... | equal _  = just (suc n)
--accumulate and keep searching
... | _        = positionInListHelper x xss (suc (suc n))

positionInList : ℕ → List ℕ → Maybe ℕ
positionInList n ns = positionInListHelper n ns zero

-- We usually assume the "husbands" to be the proposing side,
-- therefore if women propose instead the pair will
-- look like (wife, husband)
getPartner : (person : ℕ) → (couples : List (ℕ × ℕ)) → Maybe ℕ
--not married yet and this is the first proposal in the algorithm!
getPartner person [] = nothing
getPartner person ((m , w) ∷ []) with compare person w
... | equal _ = just m --found your husband!
... | _       = nothing --not married yet
getPartner person ((m , w) ∷ (c ∷ cs)) with compare person w
... | equal _ = just m --found your husband!
... | _       = getPartner person (c ∷ cs) --keep searching

-- Simply extract a preference list from the scheme of indexed lists.
getPreferenceList : ℕ → List (ℕ × List ℕ) → List ℕ
getPreferenceList person [] = [] --dummy case
getPreferenceList person ((p , preferences) ∷ ps) with compare person p
... | equal _ = preferences
... | _       = getPreferenceList person ps

\end{code}

Three main "operations" are performed during the execution of the algorithm which deserve special attention. In the beginning of the \emph{proposal} step a woman receives a proposal over which she mulls:

\begin{code}
-- m is the proposing man
-- h is the current husband of the woman
-- prefs is the preference list of the woman
-- returns true if the woman prefers m over h
propose : (m : ℕ)(h : ℕ)(prefs : List ℕ) → Bool
-- Woman compares
propose man h preferenceList with
        positionInList man preferenceList | positionInList h preferenceList
--does she prefer the new guy to the current one?
... | just p  | just q  = is-≤ p q
--shouldn't happen in an ideal world: proposal from an unknown man??
... | just p  | nothing = false
--shouldn't happen in an ideal world: married an unknown man previously??
... | nothing | just q  = false
--shouldn't happen in an ideal world: who are these men??
... | nothing | nothing = false

\end{code}

Here it is already possible to notice that, using pattern matching, we are forced to look at every possible case of the execution (since Agda performs termination and pattern matching completeness checkings). But some things just quite don't make sense when examined from the point of view of the Gale-Shapley algorithm: because our implementation must be type-safe, we only \emph{possibly} return a man when we search for him in a woman's preference list. Accordingly, we pattern-match on the possibility that one of the examined men (current fiance or new suitor) doesn't even exist in that woman's list!

In case the woman was previously married and accepts this new proposal, it is important that the new couple "overwrites" the previous couple in which the woman was featured, therefore we simply introduce a "safe" operation for the list update:

\begin{code}
-- Safely adding couples : previous marriages are unmade
safeAddNewCouple : (newCouple : ℕ × ℕ)(couples : List (ℕ × ℕ)) → List (ℕ × ℕ)
safeAddNewCouple (m , w) [] = (m , w) ∷ []
safeAddNewCouple (m , w) ((a , b) ∷ []) with compare w b
... | equal _ = (m , w) ∷ []
... | _       = (m , w) ∷ (a , b) ∷ []
safeAddNewCouple (m , w) ((a , b) ∷ (c ∷ cs)) with compare w b
... | equal _ = (m , w) ∷ c ∷ cs
... | _       = (a , b) ∷ safeAddNewCouple (m , w) (c ∷ cs)
\end{code}

It is perhaps worth it to stop here and examine what these implementation decisions mean for our later proofs. Since our proofs will be just functions, type-checked and computed down to normal form, the \emph{consistency} of our pattern matching definitions is key to enjoy Agda's computing power (remember: proof-checking is the same activity as type-checking). Suppose we want to prove a simple property of the $safeNewAddCouple$ operation, for example, that it indeed will work for a particular, very easy case:

\begin{code}
-- Warm up: let us prove that, if woman 3 is in the list of couples with
-- husband 1 and should now be married to husband 2, the new couple will
-- indeed be added.
p : (l : List (ℕ × ℕ))(a : ℕ) → a ≡ 3 →
    safeAddNewCouple (2 , 3) ((1 , a) ∷ l) ≡ ((2 , a) ∷ l)
\end{code}

What are the components of this proof, in other words, the parameters to this function? We provide a list, a natural number $a$, a proof that $a = 3$, and must return a proof that the operation returns a new list of couples where man 2 is married to woman 3. First we pattern match on $l$, it has two constructors, [] and \:::. Using Agda's proof assistant capabilities, we will observe that the "goal", that is, the expected type of the function return will contain the $$compare 3 a$$ application. Therefore we must use a \emph{with} construct in our proofs too in order to allow Agda to further reduce down the terms. Depending on the order in which the patterns are opened up, we might end up with different definitions for this function, here is one:

\begin{code}
p [] a e with compare 3 a
p [] zero () | w
p [] (suc zero) () | w
p [] (suc (suc zero)) () | w
p [] (suc (suc (suc zero))) e | equal .3 = refl
p [] (suc (suc (suc (suc a)))) () | w
p (x ∷ l) zero ()
p (x ∷ l) (suc .2) refl = refl
\end{code}

The clauses without a right hand side that can be seen are \emph{absurd patterns}: there is no way we can provide the proof we're hoping for when the number given as the second parameter is not 3 (in other words, \texttt{suc (suc (suc zero))} or \texttt{suc 2}...). If they were possible cases to prove, that is, cases where \emph{there would be a constructor} for the type we hope to achieve, we might for example open up a second \emph{with} construct where in this case only $| w$ was left by Agda, and continue pattern matching and reducing further and further from there until we are able to construct the goal.

In a similar fashion, when the list of engaged men is updated, the previous husband must be removed from it. Ww give two versions for this function, one which simply returns the updated $engagedMen$ list and another one which returns also some extra information (the man who was dumped and goes back to being free). The reasons why are further discussed later in this chapter.

\begin{code}
-- Safely adding new engaged men to the list : dumped man is removed
safeAddNewEngagedMan : (newEngagedMan : (ℕ × List ℕ))
                       (prevFiance : ℕ)
                       (prevEngagedMen : List (ℕ × List ℕ))
                       → List (ℕ × List ℕ)
-- Dummy case: this function is only invoked if a woman is already
-- married, so the list of engaged men can not possibly be empty...
safeAddNewEngagedMan (newFiance , prefs) prevFiance [] = (newFiance , prefs) ∷ []

safeAddNewEngagedMan (newFiance , prefs) prevFiance ((m , prefsM) ∷ [])
                     with compare prevFiance m
--kick him out!
... | equal _ = (newFiance , prefs) ∷ []
--safe to keep after all
... | _       = (newFiance , prefs) ∷ (m , prefsM) ∷ []
safeAddNewEngagedMan (newFiance , prefs) prevFiance ((m , prefsM) ∷ ms ∷ engagedMen)
                     with compare prevFiance m
--kick him out!
... | equal _ = (newFiance , prefs) ∷ ms ∷ engagedMen
--safe to keep... for now
... | _       = (m , prefsM) ∷
                safeAddNewEngagedMan (newFiance , prefs)
                                     prevFiance
                                     (ms ∷ engagedMen)

-- We give an alternative version which doesn't lose information:
-- it also returns the dumped man in a pair, or a dummy man
-- with an empty list. This helps Agda keep track of the length
-- of the preference lists in the matching state
safeAddNewEngagedMan′ : (newEngagedMan : (ℕ × List ℕ))
                        (prevFiance : ℕ)
                        (prevEngagedMen : List (ℕ × List ℕ))
                        → (List (ℕ × List ℕ)) × (ℕ × List ℕ)
safeAddNewEngagedMan′ (newFiance , prefs) prevFiance [] =
                      ((newFiance , prefs) ∷ [] , (0 , []))
safeAddNewEngagedMan′ (newFiance , prefs) prevFiance ((m , prefsM) ∷ [])
                      with compare prevFiance m
... | equal _ = ((newFiance , prefs) ∷ [] , (m , prefsM))
... | _       = (((newFiance , prefs) ∷ (m , prefsM) ∷ []) , (0 , []))
safeAddNewEngagedMan′ (newFiance , prefs) prevFiance ((m , prefsM) ∷ ms ∷ engagedMen)
                with compare prevFiance m
... | equal _ = ((newFiance , prefs) ∷ ms ∷ engagedMen , (m , prefsM))
... | _       = (m , prefsM) ∷ (proj₁ (safeAddNewEngagedMan′ (newFiance , prefs) prevFiance (ms ∷ engagedMen))) ,
                proj₂ (safeAddNewEngagedMan′ (newFiance , prefs) prevFiance (ms ∷ engagedMen))
\end{code}

Finally, we are ready to implement a step of the Gale-Shapley algorithm by pattern matching on the matching state. There are two main cases to be distinguished:

\begin{itemize}
    \item There is still a free man with a woman to propose to on his list: we make the proposal, update the state accordingly and return the matching. This case is the third case of the pattern matching in the function below;
    \item There are no more free men: we return the current state as the final (and stable) matching state. That is our base case.
\end{itemize}

We detail them further in the comments:

\begin{code}
step : MatchingState → MatchingState
-- When there are no more free men, the matching is stable and this is the last step.
step (mkState men [] engagedMen women couples k p) = mkState men [] engagedMen women couples k p

-- Dummy case : the function shouldn't really be invoked with a man with empty
-- preferences. But otherwise Agda would question the completeness of our
-- pattern matching.
step (mkState men ((n , []) ∷ freeMen) engagedMen women couples k p) =
     mkState men freeMen engagedMen women couples k p

-- Proposal step
step (mkState men ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples k p) with getPartner w couples

-- First case: woman w has a husband h, represented by his literal number.
-- In this case
... | just h with propose n h (getPreferenceList w women)
...               | true  = mkState men freeMenUpdated engagedMenUpdated women
                            (safeAddNewCouple (n , w) couples)
                            (compSumPrefLists freeMenUpdated engagedMenUpdated) refl
                           where
                               freeMenUpdated    =
                                 proj₂ (safeAddNewEngagedMan′ (n , prefs) h engagedMen) ∷ freeMen
                               engagedMenUpdated =
                                 proj₁ (safeAddNewEngagedMan′ (n , prefs) h engagedMen)
...               | false = mkState men ((n , prefs) ∷ freeMen) engagedMen women
                            couples
                            (compSumPrefLists ((n , prefs) ∷ freeMen) engagedMen) refl

-- Second case: woman w didn't have a husband yet: simply must accept proposal
step (mkState men ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples k p) | nothing
     = mkState men freeMen ((n , prefs) ∷ engagedMen) women (safeAddNewCouple (n , w) couples)
               (compSumPrefLists freeMen ((n , prefs) ∷ engagedMen)) refl

\end{code}

In order to calculate a final result we just apply the step function 

\begin{code}
{-# TERMINATING #-}
allSteps : (m : MatchingState)(k : ℕ) → k ≡ MatchingState.sumPrefLists m → MatchingState
allSteps m k p with step m
... | mkState men [] engagedMen women couples k₁ p₁ = mkState men [] engagedMen women couples k₁ p₁
... | m' = allSteps m' (MatchingState.sumPrefLists m') refl
\end{code}

-- (compSumPrefLists (MatchingState.freeMen m') (MatchingState.engagedMen m')

\section{Proofs on Gale-Shapley algorithm}

\subsection{Termination}



\begin{code}
+-zero : ∀ n k → k ≡ n + 0 → k ≡ n
+-zero zero zero p = p
+-zero zero (suc k) p = p
+-zero (suc n) zero ()
+-zero (suc n) (suc .(n + 0)) refl = cong suc (+-identityʳ n)

+-move-zero : ∀ n k → k ≡ n + 0 → n ≡ k + 0
+-move-zero zero zero refl = refl
+-move-zero zero (suc k) ()
+-move-zero (suc n) zero ()
+-move-zero (suc n) (suc .(n + 0)) refl = cong suc (+-move-zero n (n + 0) refl)

n≤n+m : ∀ m n → n ≤′ n + m
n≤n+m zero zero = ≤′-refl
n≤n+m zero (suc m) =  ≤⇒≤′ (≤-reflexive (cong suc (sym (+-identityʳ m))))
n≤n+m (suc n) zero = ≤′-step (n≤n+m n zero)
n≤n+m (suc n) (suc m) = s≤′s (n≤n+m (suc n) m)

n+m≤n+m+s : ∀ (m n s : ℕ) → n + m ≤ n + m + s
n+m≤n+m+s zero zero zero = z≤n
n+m≤n+m+s zero zero (suc s) = z≤n
n+m≤n+m+s zero (suc m) zero = s≤s (n+m≤n+m+s zero m zero)
n+m≤n+m+s zero (suc m) (suc s) = s≤s (n+m≤n+m+s zero m (suc s))
n+m≤n+m+s (suc n) zero zero = s≤s (n+m≤n+m+s n zero zero)
n+m≤n+m+s (suc n) zero (suc s) = s≤s (n+m≤n+m+s n zero (suc s))
n+m≤n+m+s (suc n) (suc m) zero = s≤s (n+m≤n+m+s (suc n) m zero)
n+m≤n+m+s (suc n) (suc m) (suc s) = s≤s (n+m≤n+m+s (suc n) m (suc s))

{--
lengthPrefsOneSide : ∀ (freeMen engagedMen : List (ℕ × List ℕ))(k : ℕ) → k ≡ compSumPrefLists freeMen engagedMen → (lengthPrefs freeMen ≤′ k) × (lengthPrefs engagedMen ≤′ k)
lengthPrefsOneSide [] [] k p = z≤′n , z≤′n
lengthPrefsOneSide [] ((fst , []) ∷ engagedMen) k p = z≤′n , proj₂ (lengthPrefsOneSide [] engagedMen k p)
lengthPrefsOneSide [] ((fst , x ∷ snd) ∷ engagedMen) k p = z≤′n , ≤⇒≤′ (≤-reflexive (sym p))
lengthPrefsOneSide ((fst , []) ∷ freeMen) [] k p = ≤⇒≤′ (≤-reflexive (+-zero k (lengthPrefs freeMen) (+-move-zero (lengthPrefs freeMen) k p))) , z≤′n
lengthPrefsOneSide ((fst , x ∷ snd) ∷ freeMen) [] k p = ≤⇒≤′ (≤-reflexive (+-zero k (lengthPrefs ((fst , x ∷ snd) ∷ freeMen)) (+-move-zero (suc (lengthPrefs ((fst , snd) ∷ freeMen))) k p))) , z≤′n
lengthPrefsOneSide ((fst , []) ∷ freeMen) ((fst₁ , []) ∷ engagedMen) k p = lengthPrefsOneSide freeMen engagedMen k p
lengthPrefsOneSide ((fst , []) ∷ freeMen) ((fst₁ , x ∷ snd₁) ∷ engagedMen) .(lengthPrefs freeMen + suc (lengthPrefs ((fst₁ , snd₁) ∷ engagedMen))) refl = proj₁ (lengthPrefsOneSide freeMen ((fst₁ , x ∷ snd₁) ∷ engagedMen) (lengthPrefs freeMen + suc (lengthPrefs ((fst₁ , snd₁) ∷ engagedMen))) refl) , ≤⇒≤′ (n≤m+n (lengthPrefs freeMen) (suc (lengthPrefs ((fst₁ , snd₁) ∷ engagedMen))))
lengthPrefsOneSide ((fst , x ∷ snd) ∷ freeMen) ((fst₁ , []) ∷ engagedMen) .(suc (lengthPrefs ((fst , snd) ∷ freeMen) + lengthPrefs engagedMen)) refl = ≤⇒≤′ (s≤s (n+m≤n+m+s (lengthPrefs freeMen) (length snd) (lengthPrefs engagedMen))) , proj₂ (lengthPrefsOneSide ((fst , x ∷ snd) ∷ freeMen) engagedMen ((suc (lengthPrefs ((fst , snd) ∷ freeMen) + lengthPrefs engagedMen))) (cong suc refl)) 
lengthPrefsOneSide ((fst , x ∷ snd) ∷ freeMen) ((fst₁ , x₁ ∷ snd₁) ∷ engagedMen) p refl = n≤n+m (suc (lengthPrefs ((fst₁ , snd₁) ∷ engagedMen))) (suc (lengthPrefs ((fst , snd) ∷ freeMen))) , ≤⇒≤′ (n≤m+n (lengthPrefs ((fst , x ∷ snd) ∷ freeMen)) (lengthPrefs ((fst₁ , x₁ ∷ snd₁) ∷ engagedMen)))
--}

stepsWithPrefs : ∀ m n → m ≤ n → m ≤ 1 + n
stepsWithPrefs zero zero z≤n = z≤n
stepsWithPrefs zero (suc n) z≤n = z≤n
stepsWithPrefs (suc m) zero ()
stepsWithPrefs (suc m) (suc n) (s≤s p₁) = s≤s (stepsWithPrefs m n p₁)

m≤n+r+m : ∀ m n r → m ≤′ n + suc (r + m)
m≤n+r+m zero zero zero = z≤′n
m≤n+r+m zero zero (suc r) = z≤′n
m≤n+r+m zero (suc n) zero = z≤′n
m≤n+r+m zero (suc n) (suc r) = z≤′n
m≤n+r+m (suc m) zero zero = s≤′s (m≤n+r+m m zero zero)
m≤n+r+m (suc m) zero (suc r) = m≤n+r+m (suc m) 1 r
m≤n+r+m (suc m) (suc n) zero = s≤′s (m≤n+r+m m n 1)
m≤n+r+m (suc m) (suc n) (suc r) = ≤′-step (m≤n+r+m (suc m) n (suc r))

lengthPrefsExtLemma : ∀ (x : ℕ × List ℕ)(xs : List (ℕ × List ℕ))(n : ℕ) → lengthPrefs xs ≤′ n + lengthPrefs (x ∷ xs)
lengthPrefsExtLemma (man , prefs) [] n = z≤′n
lengthPrefsExtLemma (man , []) ((fst , []) ∷ ms) n = n≤′m+n n (lengthPrefs ms)
lengthPrefsExtLemma (man , x ∷ prefs) ((fst , []) ∷ ms) n = lengthPrefsExtLemma (man , x ∷ prefs) ms n
lengthPrefsExtLemma (man , []) ((fst , w ∷ ws) ∷ ms) n = n≤′m+n n (suc (lengthPrefs ((fst , ws) ∷ ms)))
lengthPrefsExtLemma (man , x ∷ prefs) ((fst , w ∷ ws) ∷ ms) n = m≤n+r+m (suc (length ws + lengthPrefs ms)) n (length prefs)

n≤1+n-plus-zero : ∀ n → n ≤ suc (n + 0)
n≤1+n-plus-zero zero = z≤n
n≤1+n-plus-zero (suc n) = s≤s (n≤1+n-plus-zero n)

n-plus-zero≤1+n+m : ∀ m n → n + 0 ≤ suc (n + m)
n-plus-zero≤1+n+m zero zero = z≤n
n-plus-zero≤1+n+m zero (suc n) = s≤s (n-plus-zero≤1+n+m zero n)
n-plus-zero≤1+n+m (suc m) zero = z≤n
n-plus-zero≤1+n+m (suc m) (suc n) = s≤s (n-plus-zero≤1+n+m (suc m) n)

n≤2+m+n : ∀ m n → n + 0 ≤′ suc (suc (m + n) + 0)
n≤2+m+n zero zero = ≤′-step (≤′-step ≤′-refl)
n≤2+m+n zero (suc n) = ≤′-step (≤′-step ≤′-refl)
n≤2+m+n (suc m) zero = ≤′-step (n≤2+m+n m zero)
n≤2+m+n (suc m) (suc n) = ≤′-step (n≤2+m+n m (suc n))

\end{code}

For the following proofs we might 


\begin{code}
import Data.Nat.Solver
open Data.Nat.Solver.+-*-Solver
  using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)

lem2 : (4 + 6 ≡ 10)
lem2 = solve 0 (con 4 :+ con 6 := con 10) refl

lem3 : (x : ℕ) → (2 * (x + 4) ≡ 8 + 2 * x)
lem3 = solve 1 (λ x' → con 2 :* (x' :+ con 4) := con 8 :+ con 2 :* x') refl

lemmaProposeTrue : ∀ (freeMen engagedMen : List (ℕ × List ℕ))(formerHusband man : ℕ)(prefs : List ℕ) →
                   length (proj₂ (proj₂ (safeAddNewEngagedMan′ (man , prefs) formerHusband engagedMen))) + lengthPrefs freeMen + lengthPrefs (proj₁ (safeAddNewEngagedMan′ (man , prefs) formerHusband engagedMen))
                   ≤′ suc (length prefs + lengthPrefs freeMen + lengthPrefs engagedMen)
lemmaProposeTrue freeMen [] formerHusband man prefs = subst (λ x → lengthPrefs freeMen + (length prefs + 0) ≤′ suc x)
                                                             (solve 2 (λ x y → x :+ (y :+ con 0) := (y :+ x :+ con 0)) refl (lengthPrefs freeMen) (length prefs))
                                                             (≤⇒≤′ (n≤1+n _))
lemmaProposeTrue freeMen ((m , prefsM) ∷ []) formerHusband man prefs with compare formerHusband m
lemmaProposeTrue freeMen ((.(suc (formerHusband + k)) , prefsM) ∷ []) formerHusband man prefs | less .formerHusband k = subst (λ x → lengthPrefs freeMen + (length prefs + (length prefsM + 0)) ≤′ suc x)
                                                                                                                               (solve 3 (λ x y z → x :+ (y :+ (z :+ con 0)) := y :+ x :+ (z :+ con 0)) refl (lengthPrefs freeMen) (length prefs) (length prefsM))
                                                                                                                               (≤⇒≤′ (n≤1+n _))
lemmaProposeTrue freeMen ((m , prefsM) ∷ []) .m man prefs | equal .m = subst (λ x → length prefsM + lengthPrefs freeMen + (length prefs + 0) ≤′ suc x)
                                                                              (solve 3 (λ x y z → x :+ y :+ (z :+ con 0) := z :+ y :+ (x :+ con 0)) refl (length prefsM) (lengthPrefs freeMen) (length prefs))
                                                                              (≤⇒≤′ (n≤1+n _))
lemmaProposeTrue freeMen ((m , prefsM) ∷ []) .(suc (m + k)) man prefs | greater .m k = subst (λ x → lengthPrefs freeMen + (length prefs + (length prefsM + 0)) ≤′ suc x)
                                                                                              (solve 3 (λ x y z → x :+ (y :+ (z :+ con 0)) := y :+ x :+ (z :+ con 0)) refl (lengthPrefs freeMen) (length prefs) (length prefsM))
                                                                                              (≤⇒≤′ (n≤1+n _))
lemmaProposeTrue freeMen ((m , prefsM) ∷ ms ∷ engagedMen) formerHusband man prefs with compare formerHusband m
lemmaProposeTrue freeMen ((.(suc (formerHusband + k)) , prefsM) ∷ ms ∷ engagedMen) formerHusband man prefs | less .formerHusband k with safeAddNewEngagedMan′ (man , prefs) formerHusband (ms ∷ engagedMen)
lemmaProposeTrue freeMen ((.(suc (formerHusband + k)) , prefsM) ∷ ms ∷ engagedMen) formerHusband man prefs | less .formerHusband k | updatedEngagedMen , extraInfo = {!!}
lemmaProposeTrue freeMen ((m , prefsM) ∷ ms ∷ engagedMen) .m man prefs | equal .m = subst (λ x → length prefsM + lengthPrefs freeMen + (length prefs + (length (proj₂ ms) + lengthPrefs engagedMen)) ≤′ suc x)
                                                                                           (solve 5 (λ u v w y z → u :+ v :+ (w :+ (y :+ z)) := w :+ v :+ (u :+ (y :+ z))) refl                                                                                                  (length prefsM) (lengthPrefs freeMen) (length prefs) (length (proj₂ ms)) (lengthPrefs engagedMen))
                                                                                           (≤⇒≤′ (n≤1+n _))
lemmaProposeTrue freeMen ((m , prefsM) ∷ ms ∷ engagedMen) .(suc (m + k)) man prefs | greater .m k with safeAddNewEngagedMan′ (man , prefs) (suc (m + k)) (ms ∷ engagedMen)
lemmaProposeTrue freeMen ((m , prefsM) ∷ ms ∷ engagedMen) .(suc (m + k)) man prefs | greater .m k | updatedEngagedMen , extraInfo = {!!}


decompLemma : ∀ n prefs engagedMen x₁ → lengthPrefs ((n , prefs) ∷ x₁ ∷ engagedMen) ≤ suc (lengthPrefs ((n , prefs) ∷ []) + lengthPrefs (x₁ ∷ engagedMen))
decompLemma n [] engagedMen x₁ = n≤1+n _
decompLemma n (x ∷ prefs) engagedMen (fst , []) = s≤s (decompLemma n prefs engagedMen (fst , []))
decompLemma n (x ∷ prefs) engagedMen (fst , x₁ ∷ snd) = s≤s (decompLemma n prefs engagedMen (fst , x₁ ∷ snd))

singleWomanLemma : ∀ freeMen n prefs engagedMen →
  lengthPrefs freeMen + lengthPrefs ((n , prefs) ∷ engagedMen) ≤′
  suc (lengthPrefs ((n , prefs) ∷ freeMen) + lengthPrefs engagedMen)
singleWomanLemma freeMen n prefs engagedMen = subst (λ x → lengthPrefs freeMen + lengthPrefs ((n , prefs) ∷ engagedMen) ≤′ suc x)
                                                (solve 3 (λ x y z → x :+ (y :+ z) := y :+ x :+ z) refl (lengthPrefs freeMen) (length prefs) (lengthPrefs engagedMen))
                                                (≤⇒≤′ (n≤1+n _))

stepDec : (m : MatchingState) → compSumPrefLists (MatchingState.freeMen m) (MatchingState.engagedMen m) ≥′ compSumPrefLists (MatchingState.freeMen (step m)) (MatchingState.engagedMen (step m))
stepDec (mkState men [] [] women couples k p) = ≤′-refl
stepDec (mkState men [] ((man , prefs) ∷ engagedMen) women couples k p) = ≤′-refl
stepDec (mkState men ((man , []) ∷ freeMen) engagedMen women couples k p) = ≤′-refl
stepDec (mkState men ((man , w ∷ prefs) ∷ freeMen) engagedMen women couples k p) with getPartner w couples
...             | just h with propose man h (getPreferenceList w women)
...             | true  = lemmaProposeTrue freeMen engagedMen h man prefs
...             | false = ≤⇒≤′ (n≤1+n _)
stepDec (mkState men ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples k p) | nothing = singleWomanLemma freeMen n prefs engagedMen

\end{code}

Now let us examine some examples. We look at the two cases from Gale and Shapley's original paper, one where we have an uncomplicated setup for which the deferred acceptance algorithm gives every man the first possible choice of woman, and another where there is in fact only one possible stable set of marriages and the algorithm takes a longer number of steps to arrive to its final state.

\begin{code}
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

\end{code}

We now proceed to discuss the correctness of the deferred acceptance algorithm.

\begin{code}
-- The type of elements that belong to a list.
data _∈_ {A : Set}(a : A) : List A → Set where
  now   : (as : List A) → a ∈ (a ∷ as)
  later : {a' : A}{as : List A} → a ∈ as → a ∈ (a' ∷ as)

-- Bigger than comparison for Maybe ℕ-typed elements. 
data _>just_ : Maybe ℕ → Maybe ℕ → Set where
  _from>_ : {m n : ℕ} → m > n → just m >just just n

-- Helper for the condition of stability: a person is better than another one
-- in a preference list if it appears earlier in it.
_≻[_]_ : ℕ → List ℕ → ℕ → Set
person ≻[ list ] person₂ = positionInList person₂ list >just positionInList person list

-- Given a man and a woman and their preferences, the condition of stability is satisfied if
-- another m' and w' are not better positioned in their preference lists than their partners.
conditionOfStabilitySatisfied : (c₁ : (ℕ × List ℕ) × (ℕ × List ℕ))(c₂ : (ℕ × List ℕ) × (ℕ × List ℕ)) → Set
conditionOfStabilitySatisfied ((m , prefsM) , w , prefsW) ((m' , prefsM') , w' , prefsW') =
  (¬ ( ( w' ≻[ prefsM ] w ) ×  ( m ≻[ prefsW' ] m' ))) × (¬ ( (w ≻[ prefsM' ] w') × (m' ≻[ prefsW ] m)))

-- A matching is stable if the condition of stability is satisfied for every pair of man and woman not married.
is-stable-matching : MatchingState → Set
is-stable-matching (mkState men freeMen engagedMen women couples k p) =
  (freeMen ≡ []) × (
      (c₁ c₂ : ℕ × ℕ) → c₁ ∈ couples → c₂ ∈ couples → ¬ (c₁ ≡ c₂) → 
          conditionOfStabilitySatisfied 
            ( ( (proj₁ c₁) , getPreferenceList (proj₁ c₁) men) , ( (proj₂ c₁) , getPreferenceList (proj₂ c₁) women))
            ( ( (proj₁ c₂) , getPreferenceList (proj₁ c₂) men) , ( (proj₂ c₂) , getPreferenceList (proj₂ c₂) women)))

exStart exEnd exEndExpected : MatchingState
exStart       = mkState listMen listMen [] listWomen [] 9 refl
-- Gale and Shapley tell us that, for the first simple example, each men gets his first woman from the list as a wife
-- and there are no conflicts among them. So we expect the following end state:
exEndExpected = mkState listMen [] ((3 , (1 ∷ 2 ∷ [])) ∷ ((2 , 3 ∷ 1 ∷ []) ∷ (1 , 2 ∷ 3 ∷ []) ∷ [] )) listWomen ((2 , 2) ∷ (3 , 3) ∷ (1 , 1) ∷ []) 6 refl
exEnd         = step (step (step (step exStart)))

resultIsWhatWeExpected : exEnd ≡ exEndExpected
resultIsWhatWeExpected = refl

ex2Start ex2End ex2EndExpected : MatchingState
ex2Start         = mkState listDifficultMen listDifficultMen [] listDifficultWomen [] 16 refl
-- A second, harder example is given where there is only one possible stable set of marriages.
ex2EndExpected   = mkState listDifficultMen [] ((1 , ( 4 ∷ [] )) ∷ (4 , (3 ∷ 1 ∷ [])) ∷ (2 , ( 3 ∷ 2 ∷ [] )) ∷ (3 , ( 3 ∷ 4 ∷ [])) ∷ []) listDifficultWomen (((2 , 4) ∷ (4 , 2) ∷ (1 , 3) ∷ (3 , 1) ∷ [])) 7 refl
ex2End           = step (step (step (step (step (step (step (step (step ex2Start))))))))

result2IsWhatWeExpected : ex2End ≡ ex2EndExpected
result2IsWhatWeExpected = refl


matchIsStableHelper : (c₁ c₂ : ℕ × ℕ)  →
      c₁ ∈ MatchingState.couples exEnd →
      c₂ ∈ MatchingState.couples exEnd →
      ¬ (c₁ ≡ c₂) →
       conditionOfStabilitySatisfied
      (((proj₁ c₁) , (getPreferenceList (proj₁ c₁) (MatchingState.men exEnd))) , ((proj₂ c₁) , (getPreferenceList (proj₂ c₁) (MatchingState.women exEnd))))
      (((proj₁ c₂) , (getPreferenceList (proj₁ c₂) (MatchingState.men exEnd))) , ((proj₂ c₂) , (getPreferenceList (proj₂ c₂) (MatchingState.women exEnd))))
matchIsStableHelper _ _ (now .((3 , 3) ∷ (1 , 1) ∷ []))
                        (now .((3 , 3) ∷ (1 , 1) ∷ []))
                        p = ⊥-elim (p refl) , ⊥-elim (p refl)
matchIsStableHelper _ _ (now .((3 , 3) ∷ (1 , 1) ∷ []))
                        (later (now .((1 , 1) ∷ [])))
                        p = (λ { (_from>_ () , _) }) , λ { (_from>_ () , _) }
matchIsStableHelper _ _ (now .((3 , 3) ∷ (1 , 1) ∷ []))
                        (later (later (now .[])))
                        p = (λ { (_from>_ () , _) }) , λ { (_from>_ () , _) }
matchIsStableHelper _ _ (now .((3 , 3) ∷ (1 , 1) ∷ []))
                        (later (later (later ())))
                        p
matchIsStableHelper _ _ (later (now .((1 , 1) ∷ [])))
                        (now .((3 , 3) ∷ (1 , 1) ∷ []))
                        p = (λ { (_from>_ () , _) }) , λ { (_from>_ () , _) }
matchIsStableHelper _ _ (later (now .((1 , 1) ∷ [])))
                        (later (now .((1 , 1) ∷ [])))
                        p = ⊥-elim (p refl)
matchIsStableHelper _ _ (later (now .((1 , 1) ∷ [])))
                        (later (later (now .[])))
                        p = (λ { (_from>_ () , _) }) , λ { (_from>_ () , _) }
matchIsStableHelper _ _ (later (now .((1 , 1) ∷ [])))
                        (later (later (later ())))
matchIsStableHelper _ _ (later (later (now .[])))
                        (now .((3 , 3) ∷ (1 , 1) ∷ []))
                        p = (λ { (_from>_ () , _) }) , λ { (_from>_ () , _) }
matchIsStableHelper _ _ (later (later (now .[])))
                        (later (now .((1 , 1) ∷ [])))
                        p = (λ { (_from>_ () , _) }) , λ { (_from>_ () , _) }
matchIsStableHelper _ _ (later (later (now .[])))
                        (later (later (now .[])))
                        p = ⊥-elim (p refl)
matchIsStableHelper _ _ (later (later (now .[])))
                        (later (later (later ())))
matchIsStableHelper _ _ (later (later (later ()))) _ _

matchIsStable : is-stable-matching exEnd
matchIsStable = refl , matchIsStableHelper

-- In order to define that a matching m₁ is better than a matching m₂,
-- we take into consideration that for all men they get a better
-- (earlier in their list) wife in m₁ than in m₂; this can be seen
-- from the size of his preference list in the final state of matching. 
is-better-matching : (m₁ m₂ : MatchingState) → Set
is-better-matching (mkState men freeMen engagedMen women couples k p)
                   (mkState men₁ freeMen₁ engagedMen₁ women₁ couples₁ k₁ p₁) =
                   is-stable-matching (mkState men freeMen engagedMen women couples k p) ×
                   is-stable-matching (mkState men₁ freeMen₁ engagedMen₁ women₁ couples₁ k₁ p₁) ×
                   ((m₁ m₂ : ℕ × List ℕ) → m₁ ∈ engagedMen →  m₂ ∈ engagedMen₁ →
                   proj₁ m₁ ≡ proj₁ m₂ →
                   getPreferenceList (proj₁ m₁) men ≡ getPreferenceList (proj₁ m₂) men₁ →
                   length (proj₂ m₁) ≥ length (proj₂ m₂))


-- Let us demonstrate with the first canonical example. Gale and Shapley tell us
-- that another possible stable marriage (not returned by their algorithm) is obtained
-- by giving every woman her first choice:
anotherPossibleStableMatching : MatchingState
anotherPossibleStableMatching = mkState listMen [] ((3 , []) ∷ (1 , []) ∷ (2 , []) ∷ []) listWomen ((3 , 2) ∷ (1 , 3) ∷ (2 , 1) ∷ []) _ refl

anotherMatchIsStableHelper : (c₁ c₂ : ℕ × ℕ) →
      c₁ ∈ MatchingState.couples anotherPossibleStableMatching →
      c₂ ∈ MatchingState.couples anotherPossibleStableMatching →
      ¬ c₁ ≡ c₂ →
      conditionOfStabilitySatisfied
      (((proj₁ c₁) , (getPreferenceList (proj₁ c₁) (MatchingState.men anotherPossibleStableMatching))) , ((proj₂ c₁) , (getPreferenceList (proj₂ c₁) (MatchingState.women anotherPossibleStableMatching))))
      (((proj₁ c₂) , (getPreferenceList (proj₁ c₂) (MatchingState.men anotherPossibleStableMatching))) , ((proj₂ c₂) , (getPreferenceList (proj₂ c₂) (MatchingState.women anotherPossibleStableMatching))))
anotherMatchIsStableHelper _ _ (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               p = ⊥-elim (p refl)
anotherMatchIsStableHelper _ _ (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               (later (now .((2 , 1) ∷ [])))
                               p = (λ { (_ , _from>_ ()) }) , λ { (_ , _from>_ ()) }
anotherMatchIsStableHelper _ _ (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               (later (later (now .[])))
                               p = (λ { (_ , _from>_ ()) }) , λ { (_ , _from>_ ()) }
anotherMatchIsStableHelper _ _ (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               (later (later (later ())))
                               p
anotherMatchIsStableHelper _ _ (later (now .((2 , 1) ∷ [])))
                               (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               p = (λ { (_ , _from>_ ()) }) , λ { (_ , _from>_ ()) } 
anotherMatchIsStableHelper _ _ (later (later (now .[])))
                               (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               p = (λ { (_ , _from>_ ()) }) , λ { (_ , _from>_ ()) }
anotherMatchIsStableHelper _ _ (later (later (later ())))
                               (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               p
anotherMatchIsStableHelper _ _ (later (now .((2 , 1) ∷ [])))
                               (later (now .((2 , 1) ∷ [])))
                               p = ⊥-elim (p refl)
anotherMatchIsStableHelper _ _ (later (now .((2 , 1) ∷ [])))
                               (later (later (now .[])))
                               p = (λ { (_ , _from>_ ()) }) , λ { (_ , _from>_ ()) }
anotherMatchIsStableHelper _ _ (later (now .((2 , 1) ∷ [])))
                               (later (later (later ())))
                               p
anotherMatchIsStableHelper _ _ (later (later (now .[])))
                               (later (now .((2 , 1) ∷ [])))
                               p = (λ { (_ , _from>_ ()) }) , λ { (_ , _from>_ ()) }
anotherMatchIsStableHelper _ _ (later (later (later ())))
                               (later (now .((2 , 1) ∷ [])))
                               p
anotherMatchIsStableHelper _ _ (later (later (now .[])))
                               (later (later (now .[])))
                               p = ⊥-elim (p refl)
anotherMatchIsStableHelper _ _ (later (later (now .[])))
                               (later (later (later ())))
                               p
anotherMatchIsStableHelper _ _ (later (later (later ())))
                               (later (later (now .[])))
                               p
anotherMatchIsStableHelper _ _ (later (later (later ())))
                               (later (later (later c₂)))
                               p

itIsAlsoStable : is-stable-matching anotherPossibleStableMatching
itIsAlsoStable = refl , anotherMatchIsStableHelper

matchIsBetterHelper : (m₁ m₂ : Σ ℕ (λ x → List ℕ)) →
      m₁ ∈ MatchingState.engagedMen exEnd →
      m₂ ∈ MatchingState.engagedMen anotherPossibleStableMatching →
      proj₁ m₁ ≡ proj₁ m₂ →
      (getPreferenceList (proj₁ m₁) listMen
      ≡
      getPreferenceList (proj₁ m₂) listMen)
      →
      length (proj₂ m₁) ≥ length (proj₂ m₂)
matchIsBetterHelper .(3 , 1 ∷ 2 ∷ []) .(3 , [])
                    (now .((2 , 3 ∷ 1 ∷ []) ∷ (1 , 2 ∷ 3 ∷ []) ∷ []))
                    (now .((1 , []) ∷ (2 , []) ∷ [])) p₃ p₄ = z≤n
matchIsBetterHelper .(3 , 1 ∷ 2 ∷ []) .(1 , [])
                    (now .((2 , 3 ∷ 1 ∷ []) ∷ (1 , 2 ∷ 3 ∷ []) ∷ []))
                    (later (now .((2 , []) ∷ []))) p₃ p₄ = z≤n
matchIsBetterHelper .(3 , 1 ∷ 2 ∷ []) .(2 , [])
                    (now .((2 , 3 ∷ 1 ∷ []) ∷ (1 , 2 ∷ 3 ∷ []) ∷ []))
                    (later (later (now .[]))) p₃ p₄ = z≤n
matchIsBetterHelper .(3 , 1 ∷ 2 ∷ []) m₂
                    (now .((2 , 3 ∷ 1 ∷ []) ∷ (1 , 2 ∷ 3 ∷ []) ∷ []))
                    (later (later (later ()))) p₃ p₄
matchIsBetterHelper .(2 , 3 ∷ 1 ∷ []) .(3 , [])
                    (later (now .((1 , 2 ∷ 3 ∷ []) ∷ [])))
                    (now .((1 , []) ∷ (2 , []) ∷ [])) p₃ p₄ = z≤n
matchIsBetterHelper .(1 , 2 ∷ 3 ∷ []) .(3 , [])
                    (later (later (now .[])))
                    (now .((1 , []) ∷ (2 , []) ∷ [])) p₃ p₄ = z≤n
matchIsBetterHelper m₁ .(3 , [])
                    (later (later (later ())))
                    (now .((1 , []) ∷ (2 , []) ∷ [])) p₃ p₄
matchIsBetterHelper .(2 , 3 ∷ 1 ∷ []) .(1 , [])
                    (later (now .((1 , 2 ∷ 3 ∷ []) ∷ [])))
                    (later (now .((2 , []) ∷ []))) p₃ p₄ = z≤n
matchIsBetterHelper .(2 , 3 ∷ 1 ∷ []) .(2 , [])
                    (later (now .((1 , 2 ∷ 3 ∷ []) ∷ [])))
                    (later (later (now .[]))) p₃ p₄ = z≤n
matchIsBetterHelper .(2 , 3 ∷ 1 ∷ []) m₂
                    (later (now .((1 , 2 ∷ 3 ∷ []) ∷ [])))
                    (later (later (later ()))) p₃ p₄
matchIsBetterHelper .(1 , 2 ∷ 3 ∷ []) .(1 , [])
                    (later (later (now .[])))
                    (later (now .((2 , []) ∷ []))) p₃ p₄ = z≤n
matchIsBetterHelper m₁ .(1 , [])
                    (later (later (later ())))
                    (later (now .((2 , []) ∷ []))) p₃ p₄
matchIsBetterHelper .(1 , 2 ∷ 3 ∷ []) .(2 , [])
                    (later (later (now .[])))
                    (later (later (now .[]))) p₃ p₄ = z≤n
matchIsBetterHelper .(1 , 2 ∷ 3 ∷ []) m₂
                    (later (later (now .[])))
                    (later (later (later ()))) p₃ p₄
matchIsBetterHelper m₁ .(2 , [])
                    (later (later (later ())))
                    (later (later (now .[]))) p₃ p₄
matchIsBetterHelper m₁ m₂
                    (later (later (later ())))
                    (later (later (later p₂))) p₃ p₄

matchIsBetter : is-better-matching exEnd anotherPossibleStableMatching
matchIsBetter = matchIsStable , itIsAlsoStable , matchIsBetterHelper

-- Given two stable matchings m₁ , m₂ where m₁ is the result of the computation of
-- the Gale-Shapley algorithm and m₂ is a matching over the same man and women,
-- m₂ is at most as good as m₁ but no better.
{--
anyMatchIsBetter : ∀ (m m₁ m₂ : MatchingState) →
                     allSteps m (compSumPrefLists (MatchingState.freeMen m) (MatchingState.engagedMen m)) refl ≡ m₁ →
                     MatchingState.men m₂ ≡ MatchingState.men m →
                     MatchingState.women m₂ ≡ MatchingState.women m →
                     is-stable-matching m₁ → is-stable-matching m₂ →
                     is-better-matching m₁ m₂
anyMatchIsBetter m
                 (mkState men freeMen [] women couples sumPrefLists sumEq)
                 (mkState men₁ freeMen₁ [] women₁ couples₁ sumPrefLists₁ sumEq₁) p₁ p₂ p₃ (fst , snd) (fst₁ , snd₁) = (fst , snd) , (fst₁ , snd₁) , {!!}
anyMatchIsBetter m (mkState men freeMen [] women couples sumPrefLists sumEq) (mkState men₁ freeMen₁ (x ∷ engagedMen₁) women₁ couples₁ sumPrefLists₁ sumEq₁) p₁ p₂ p₃ (fst , snd) (fst₁ , snd₁) = {!!}
anyMatchIsBetter m (mkState men freeMen (x ∷ engagedMen) women couples sumPrefLists sumEq) (mkState men₁ freeMen₁ [] women₁ couples₁ sumPrefLists₁ sumEq₁) p₁ p₂ p₃ (fst , snd) (fst₁ , snd₁) = {!!}
anyMatchIsBetter m (mkState men freeMen (x ∷ engagedMen) women couples sumPrefLists sumEq) (mkState men₁ freeMen₁ (x₁ ∷ engagedMen₁) women₁ couples₁ sumPrefLists₁ sumEq₁) p₁ p₂ p₃ (fst , snd) (fst₁ , snd₁) = {!!}
-}

leftInv : (a : ℕ) → zero + a ≡ a
leftInv a = refl

rightInv : (a : ℕ) → a + zero ≡ a
rightInv zero = refl
rightInv (suc a) = cong suc (rightInv a)

\end{code}}
