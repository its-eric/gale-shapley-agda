\newcommand{\GaleShapley}{%

To define the Gale-Shapley algorithm in Agda, we need a data structure which captures the state of the procedure in its various elements, in order to reason about its properties in an expressive enough manner that proofs can be written in the same manner as we have reasoned logically about the properties of the algorithm in Chapter \ref{Chapter3}. We make use here of Agda's record types.

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

We expect to start the execution of the algorithm with a copy of all men in the $freeMen$ list, and finish with all of them in $engagedMen$. A list of couples can then be extracted from $couples$. The lists $men$ and $women$ are preserved throughout the execution; the reason behind this particular design decision is to facilitate the writing of predicates in Agda, since, as introduced before, proofs involving the Gale-Shapley algorithm may discuss, at the same time, the "absolute" preference list of men and women or the \emph{current state} of their preference lists at a certain step of the algorithm. Therefore the current state of a certain man's preference list can be observed either in this or that list given that the man is free or engaged at a certain point during the execution.

We give two extra implementation-specific components: we keep track of the sum of preference lists of men, and provide a proof at all times that this number is in fact equal to the sum if it is computed.

Some helper functions are defined as tools to support the algorithm. They are defined always over pattern matching, typed with the help of Agda's case expansions. Very similar code can be written, for example, in Haskell to perform these operations over lists.

We define a function that decides whether a natural number is less than another one, in Agda style:
\begin{code}
is-≤ : ℕ → ℕ → Bool
is-≤ a b with a ≤′? b
... | Dec.yes _ = true
... | Dec.no _ = false
\end{code}

A helper function to search for an element in a list of natural numbers:

\begin{code}
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

\end{code}

A function to search for a partner in a list of couples (we usually assume the "husbands" to be the proposing side, so the couples look like \texttt{(husband, wife)}; therefore if women propose instead the pair will look like \texttt{(wife, husband)} and this function is reusable):

\begin{code}

getPartner : (person : ℕ) → (couples : List (ℕ × ℕ)) → Maybe ℕ
getPartner person [] = nothing
getPartner person ((m , w) ∷ []) with compare person w
... | equal _ = just m
... | _       = nothing
getPartner person ((m , w) ∷ (c ∷ cs)) with compare person w
... | equal _ = just m
... | _       = getPartner person (c ∷ cs)
\end{code}

A function to extract a preference list from a list of men or women:

\begin{code}
getPreferenceList : ℕ → List (ℕ × List ℕ) → List ℕ
getPreferenceList person [] = []
getPreferenceList person ((p , preferences) ∷ ps) with compare person p
... | equal _ = preferences
... | _       = getPreferenceList person ps
\end{code}

Three main "operations" are performed during the execution of the algorithm which deserve special attention. In the beginning of the \emph{proposal} step a woman receives a proposal over which she mulls:
\begin{itemize}
  \item $m$ is the proposing man,
  \item $h$ is the current husband of the woman,
  \item $prefs$ is the preference list of the woman.
\end{itemize}
The function returns true if the woman prefers $m$ over $h$.

\begin{code}
propose : (m : ℕ)(h : ℕ)(prefs : List ℕ) → Bool
propose man h preferenceList with
        positionInList man preferenceList | positionInList h preferenceList
\end{code}
This case is the interesting one: does she prefer the new guy to the current one?
\begin{code}
... | just p  | just q  = is-≤ p q
\end{code}
The next ones are added for completeness and shouldn't happen in case we give preference lists that make sense to the Gale-Shapley algorithm:
\begin{code}
-- shouldn't happen in an ideal world: proposal from an unknown man!
... | just p  | nothing = false
--shouldn't happen in an ideal world: married an unknown man previously??
... | nothing | just q  = false
--shouldn't happen in an ideal world: who are these men??
... | nothing | nothing = false

\end{code}

Here it is already possible to notice that, using pattern matching, we are forced to look at every possible case of the execution (since Agda performs termination and pattern matching completeness checkings). But some things just quite don't make sense when examined from the point of view of the Gale-Shapley algorithm: because our implementation must be type-safe, we \emph{possibly} return a man when we search for him in a woman's preference list, only if he exists in it. Accordingly, we pattern-match on the possibility that one of the examined men (current fiance or new suitor) doesn't even exist in that woman's list!

In case the woman was previously engaged and accepts this new proposal, it is important that the new couple "overwrites" the previous couple in which the woman was featured, therefore we simply introduce a "safe" operation for the list update:

\begin{code}
safeAddNewCouple : (newCouple : ℕ × ℕ)(couples : List (ℕ × ℕ)) → List (ℕ × ℕ)
safeAddNewCouple (m , w) [] = (m , w) ∷ []
safeAddNewCouple (m , w) ((a , b) ∷ []) with compare w b
... | equal _ = (m , w) ∷ []
... | _       = (m , w) ∷ (a , b) ∷ []
safeAddNewCouple (m , w) ((a , b) ∷ (c ∷ cs)) with compare w b
... | equal _ = (m , w) ∷ c ∷ cs
... | _       = (a , b) ∷ safeAddNewCouple (m , w) (c ∷ cs)
\end{code}

It is perhaps worth it to stop here and examine what these implementation decisions mean for our later proofs. Since our proofs will be just functions, type-checked and computed down to normal form, the \emph{consistency} of our pattern matching definitions is key to enjoy Agda's computing power (remember: proof-checking is the same activity as type-checking). Suppose we want to prove a simple property of the \texttt{safeNewAddCouple} operation, for example, that it will work for a particular, very easy case: let us prove that, if woman 3 is in the list of couples with husband 1 and should now be married to husband 2, the new couple will indeed be added.

\begin{code}
p : (l : List (ℕ × ℕ))(a : ℕ) → a ≡ 3 →
    safeAddNewCouple (2 , 3) ((1 , a) ∷ l) ≡ ((2 , a) ∷ l)
\end{code}

What are the components of this proof, in other words, the parameters to this function? We provide a list, a natural number $a$, a proof that $a = 3$, and must return a proof that the operation returns a new list of couples where man 2 is married to woman 3. First, we pattern match on $l$, it has two constructors, [] and ∷. Using Agda's proof assistant capabilities, we will observe that the "goal", that is, the expected type of the function return will contain the \texttt{compare 3 a} application. Therefore, we must use a \emph{with} construct in our proofs too in order to allow Agda to further reduce down the terms. Depending on the order in which the patterns are opened up, we might end up with different definitions for this function, here is one:

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

The clauses without a right hand side that can be seen are \emph{absurd patterns}: there is no way we can provide the proof we're hoping for when the number given as the second parameter is not 3 (in other words, \texttt{suc (suc (suc zero))} or \texttt{suc 2}...). If they were possible cases to prove, that is, cases where \emph{there would be a constructor} for the type we hope to achieve, we might for example open up a second \emph{with} construct where in this case only \texttt{| w} was left by Agda, and continue pattern matching and reducing further and further from there until we are able to construct the goal.

In a similar fashion, when the list of engaged men is updated, the previous husband must be removed from it. We give two versions of this function, one which simply returns the updated $engagedMen$ list and another one which returns also some extra information (the man who was dumped and goes back to being free).

\begin{code}
safeAddNewEngagedMan : (newEngagedMan : (ℕ × List ℕ))
                       (prevFiance : ℕ)
                       (prevEngagedMen : List (ℕ × List ℕ))
                       → List (ℕ × List ℕ)
\end{code}
The first one is a dummy case again: this function is only invoked if a woman is already married, so the list of engaged men cannot possibly be empty...
\begin{code}
safeAddNewEngagedMan (newFiance , prefs) prevFiance [] = (newFiance , prefs) ∷ []

safeAddNewEngagedMan (newFiance , prefs) prevFiance ((m , prefsM) ∷ [])
                     with compare prevFiance m
... | equal _ = (newFiance , prefs) ∷ []
... | _       = (newFiance , prefs) ∷ (m , prefsM) ∷ []
safeAddNewEngagedMan (newFiance , prefs) prevFiance ((m , prefsM) ∷ ms ∷ engagedMen)
                     with compare prevFiance m
... | equal _ = (newFiance , prefs) ∷ ms ∷ engagedMen
... | _       = (m , prefsM) ∷
                safeAddNewEngagedMan (newFiance , prefs)
                                     prevFiance
                                     (ms ∷ engagedMen)
\end{code}
We give an alternative version which doesn't lose information: it also returns the dumped man in a pair, or a dummy man with an empty list. This helps Agda keep track of the length of the preference lists in the matching state.
\begin{code}
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
... | _       = (m , prefsM) ∷
                (proj₁ (safeAddNewEngagedMan′ (newFiance , prefs) prevFiance (ms ∷ engagedMen)))
                ,
                proj₂ (safeAddNewEngagedMan′ (newFiance , prefs) prevFiance (ms ∷ engagedMen))
\end{code}

Finally, we are ready to implement a step of the Gale-Shapley algorithm by pattern matching on the matching state. There are two main cases to be distinguished:

\begin{itemize}
    \item There is still a free man with a woman to propose to on his list: we make the proposal, update the state accordingly and return the matching. This case is the third case of the pattern matching in the function below;
    \item There are no more free men: we return the current state as the final (and stable) matching state. That is our base case.
\end{itemize}

\begin{code}
step : MatchingState → MatchingState
-- base case
step (mkState men [] engagedMen women couples k p) =
     mkState men [] engagedMen women couples k p
\end{code}

The function shouldn't really be invoked with a man with empty preferences. But otherwise Agda would question the completeness of our pattern matching, so:

\begin{code}
step (mkState men ((n , []) ∷ freeMen) engagedMen women couples k p) =
     mkState men freeMen engagedMen women couples k p
\end{code}

And finally, our proposal step as laid out:

\begin{code}
step (mkState men ((n , w ∷ prefs) ∷ freeMen)
                  engagedMen women couples k p)
     with getPartner w couples

\end{code}
In the first case, woman $w$ has a husband $h$, represented by his literal number.
\begin{code}
... | just h with propose n h (getPreferenceList w women)
\end{code}
If she accepts the new proposal, we switch the man around in the lists of free and engaged men, and add the new couple "safely" to the list of couples.
\begin{code}
...               | true  = mkState men freeMenUpdated engagedMenUpdated women
                            (safeAddNewCouple (n , w) couples)
                            (compSumPrefLists freeMenUpdated engagedMenUpdated) refl
                           where
                             freeMenUpdated =
                               (proj₂ (safeAddNewEngagedMan′ (n , prefs) h engagedMen))
                                 ∷ freeMen
                             engagedMenUpdated =  proj₁
                                 (safeAddNewEngagedMan′ (n , prefs) h engagedMen)
\end{code}
If not, we simply give back a state in which that woman is dropped from the man's list, and he remains in the list of free men with nothing else changing.
\begin{code}
...               | false = mkState men ((n , prefs) ∷ freeMen) engagedMen women
                            couples
                            (compSumPrefLists ((n , prefs) ∷ freeMen) engagedMen)
                            refl
\end{code}
In the second case, woman $w$ didn't have a husband yet: she simply must accept the proposal.
\begin{code}
step (mkState men ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples k p)
     | nothing
     = mkState men freeMen ((n , prefs) ∷ engagedMen) women
               (safeAddNewCouple (n , w) couples)
               (compSumPrefLists freeMen ((n , prefs) ∷ engagedMen)) refl
\end{code}

In order to calculate a final result we just apply the step function until there are no more free men waiting for a wife:\footnote{We apply a special TERMINATING pragma so Agda's termination checker accepts this function: since the preference lists are hidden inside the matching state structure, it is not immediately obvious that some term is always decreasing in the recursive call. An alternative implementation could be done with the Bove-Capretta method, discussed later in this chapter.}

\begin{code}
{-# TERMINATING #-}
allSteps : (m : MatchingState) → MatchingState
allSteps (mkState men [] engagedMen women couples sumPrefLists sumEq) =
         mkState men [] engagedMen women couples sumPrefLists sumEq
allSteps m′ = allSteps (step m′)
\end{code}

\section{Proofs on the Gale-Shapley algorithm}

\subsection{Termination}

In order to provide a mathematically relevant proof of termination, we hope to prove a lemma that states that the step function decreases the sum of preference lists. This can be used, as we have seen in Chapter \ref{Chapter2}, in order to construct a proof of total correctness in the domain of Hoare logic. But how can it be done in Agda? Our goal is:

\begin{code}
stepDec : (m : MatchingState) →
          compSumPrefLists (MatchingState.freeMen m) (MatchingState.engagedMen m)
          ≥′
          compSumPrefLists (MatchingState.freeMen (step m))
                           (MatchingState.engagedMen (step m))
\end{code}

Before taking a look at this bigger proof, let us take a look at the techniques used to construct it. Agda's pattern matching and computation is extensively at play here again, as we hope to prove some facts, basically, about natural numbers. Such proofs can be easily constructed in Agda by pattern matching on the arguments of the proof (arguments of the function) further and further until we can reduce to a point where a constructor exists for the type we hope the function to return. Let us warm up with some proofs about properties of the natural numbers:

\begin{code}
leftInv : (a : ℕ) → zero + a ≡ a
leftInv a = refl

rightInv : (a : ℕ) → a + zero ≡ a
rightInv zero = refl
rightInv (suc a) = cong suc (rightInv a)
\end{code}

What is the difference between the proofs above? In the first case, if we inspect the type we hope to construct, Agda is able to reduce it from \texttt{zero + a} on the left-hand side to just \texttt{a}, since there is a pattern on the plus function definition that says \texttt{zero + m = m}. Then we can simply say that for any input, the \texttt{refl} constructor constructs a proof that \begin{math}a = a\end{math}.
For the second case, however, the \texttt{zero + m = m} definition is not enough, since we must construct a proof that \texttt{suc (a + 0) = suc a}. That almost looks like the definition of our \texttt{rightInv} function, expect for a \texttt{suc} call on both sides. The solution is to define the function recursively: \texttt{cong} adds a parameter to both sides of an equivalence. A similar solution is applied for the next proofs.

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
\end{code}

These proofs state some similar facts to the proofs before, but they \emph{take in a proof that implies our goal as a parameter}, which we may reuse in our pattern definitions: for example, in \texttt{+-zero}, in the case we get two zeroes as arguments, the definition of the plus function will simply reduce them all to \texttt{0 = 0}, which is already the proof we want. It is also interesting to notice that we don't need to give a definition for some of these cases; it will never be true that \texttt{0 = (suc k) + 0} or \texttt{(suc n) = 0 + 0} as we can see in the \texttt{+-move-zero} function, and Agda can discard these cases immediately since there are \emph{no constructors} for them.

Now onto the definition of the $\le$ operator in Agda. There are two constructors for the data type $\le$ (i.e. type of proofs about $\le$): z≤n for the cases involving zero and some other natural number $n$ and s≤s for the cases involving two numbers bigger than zero. By using extensive pattern matching, we can ask Agda to find constructors that match the types we hope to return, in fact, most of the following proofs can be written automatically by asking Agda to search for a solution:

\begin{code}
n≤1+n-plus-zero : ∀ n → n ≤ suc (n + 0)
n≤1+n-plus-zero zero = z≤n
n≤1+n-plus-zero (suc n) = s≤s (n≤1+n-plus-zero n)

n-plus-zero≤1+n+m : ∀ m n → n + 0 ≤ suc (n + m)
n-plus-zero≤1+n+m zero zero = z≤n
n-plus-zero≤1+n+m zero (suc n) = s≤s (n-plus-zero≤1+n+m zero n)
n-plus-zero≤1+n+m (suc m) zero = z≤n
n-plus-zero≤1+n+m (suc m) (suc n) = s≤s (n-plus-zero≤1+n+m (suc m) n)

n+m≤n+m+s : ∀ (m n s : ℕ) → n + m ≤ n + m + s
n+m≤n+m+s zero zero zero = z≤n
n+m≤n+m+s zero zero (suc s) = z≤n
n+m≤n+m+s zero (suc m) zero = s≤s (n+m≤n+m+s zero m zero)
n+m≤n+m+s zero (suc m) (suc s) = s≤s (n+m≤n+m+s zero m (suc s))
n+m≤n+m+s (suc n) zero zero = s≤s (n+m≤n+m+s n zero zero)
n+m≤n+m+s (suc n) zero (suc s) = s≤s (n+m≤n+m+s n zero (suc s))
n+m≤n+m+s (suc n) (suc m) zero = s≤s (n+m≤n+m+s (suc n) m zero)
n+m≤n+m+s (suc n) (suc m) (suc s) = s≤s (n+m≤n+m+s (suc n) m (suc s))
\end{code}

But how are these proofs being computed down and how does it all type-check? Let us introduce and discuss a new operator: ≤′. This is defined in Agda's standard library as an induction-friendlier alternative to $\le$. Agda also provides some conversion functions that allows us to turn proofs about ≤′ into proofs about $\le$ and vice-versa; they will feature prominently in our code in a moment. The constructors for ≤′ are \texttt{≤′-refl} and \texttt{≤′-step}:

\begin{code}
-- These are defined somewhere in the standard library:

-- data _≤′_ (m : ℕ) : ℕ → Set where
--  ≤′-refl :                         m ≤′ m
--  ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ suc n
\end{code}

In this interpretation, there are two ways of expressing $\le$: a number $m$ is always less than or equal to itself; or if it's less than or equal to another number $n$, the property will also hold for successors of $n$. With these tools we can then reconstruct what we had previously with the traditional $\le$ operator:

\begin{code}
-- z≤′n : ∀ {n} → zero ≤′ n
-- z≤′n {zero}  = ≤′-refl
-- z≤′n {suc n} = ≤′-step z≤′n

-- s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
-- s≤′s ≤′-refl        = ≤′-refl
-- s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n)
\end{code}

Now let us prove

\begin{code}
n≤n+m : ∀ m n → n ≤′ n + m
\end{code}

The first case just stems from the definition of \texttt{≤′-refl}:

\begin{code}
n≤n+m zero zero = ≤′-refl
\end{code}

The second case needs to return a proof of \texttt{suc m ≤′ suc (m + 0)}. This doesn't quite match the definition of \texttt{≤′-step}, so we fallback to ≤ to construct a proof.

\texttt{≤-reflexive} says that, if a number is equal to another number, then it is also minus than or equal to it. So we just have to give a proof that \texttt{suc m ≡ suc (m + 0)} which we construct in three steps:

\begin{enumerate}
  \item \texttt{+-identityʳ m} returns a proof that \texttt{m + 0 ≡ m};
  \item We flip the arguments with symmetry so we have \texttt{m ≡ m + 0};
  \item We apply the suc function on both sides with congruency (since \texttt{a ≡ b → f a ≡ f b}), so we have our goal proof.
\end{enumerate}

\begin{code}
n≤n+m zero (suc m) =  ≤⇒≤′ (≤-reflexive (cong suc (sym (+-identityʳ m))))
\end{code}

In the third case, although the goal is simply \texttt{zero ≤′ suc m} we can observe that our alternative operator does not immediately provide a constructor for that case as ≤ did; instead we should do it constructively with \texttt{≤′-step} applied to a recursive call. That can be deduced from the definition of the \texttt{z≤′n} function above.

\begin{code}
n≤n+m (suc n) zero = ≤′-step (n≤n+m n zero)
\end{code}

In the fourth case, we conform to the pattern of the \texttt{s≤′s} function.

\begin{code}  
n≤n+m (suc n) (suc m) = s≤′s (n≤n+m (suc n) m)
\end{code}

Onto some more computationally complicated proofs:

\begin{code}
n≤2+m+n : ∀ m n → n + 0 ≤′ suc (suc (m + n) + 0)
\end{code}

The goal for the first case is 0 ≤′ 2. With \texttt{≤′-refl} we can give a proof that 0 ≤′ 0 and then step until the number 2 with \texttt{≤′-step}: it is induction friendly, so our proof is conserved.

\begin{code}
n≤2+m+n zero zero = ≤′-step (≤′-step ≤′-refl)
\end{code}

Here the goal doesn't reduce down completely, so we must construct the type

\begin{center}
  \texttt{suc (n + 0) ≤′ suc (suc (suc (n + 0)))}
\end{center}

But we may notice that if we take \texttt{(suc (n + 0))} as a number $n$, then our goal is again to prove \texttt{n ≤ n + 2} which can be done with the same solution above:

\begin{code}
n≤2+m+n zero (suc n) = ≤′-step (≤′-step ≤′-refl)
\end{code}

For the remaining cases we can do a recursive call while beautifully stepping through the natural numbers.

\begin{code}
n≤2+m+n (suc m) zero = ≤′-step (n≤2+m+n m zero)
n≤2+m+n (suc m) (suc n) = ≤′-step (n≤2+m+n m (suc n))
\end{code}

Here is a similar function which features later in our implementation:

\begin{code}
m≤n+r+m : ∀ m n r → m ≤′ n + suc (r + m)
m≤n+r+m zero zero zero = z≤′n
m≤n+r+m zero zero (suc r) = z≤′n
m≤n+r+m zero (suc n) zero = z≤′n
m≤n+r+m zero (suc n) (suc r) = z≤′n
m≤n+r+m (suc m) zero zero = s≤′s (m≤n+r+m m zero zero)
m≤n+r+m (suc m) zero (suc r) = m≤n+r+m (suc m) 1 r
m≤n+r+m (suc m) (suc n) zero = s≤′s (m≤n+r+m m n 1)
m≤n+r+m (suc m) (suc n) (suc r) = ≤′-step (m≤n+r+m (suc m) n (suc r))
\end{code}

Now let us turn this knowledge into action with some warmup proofs about the Gale-Shapley algorithm itself. Again, Agda allows us to express ourselves quite naturally in writing down our postulates; as a first example, let us try to prove that, if a list of men is extended by a certain element (remember a man is represented by a tuple of natural number and list of natural numbers), then the length of the preference lists of that particular list is equal or bigger by some $n$ than the previous length:

\begin{code}
lengthPrefsExtLemma : ∀ (x : ℕ × List ℕ)(xs : List (ℕ × List ℕ))(n : ℕ) →
                      lengthPrefs xs ≤′ n + lengthPrefs (x ∷ xs)
\end{code}

This perhaps uninteresting, but clearly true property of our implementation can be simply proven with the use of the same elements we have discussed. Notice that we pattern match only over the function arguments which are interesting in regard to the property we are reasoning over; that is, we go as far as examining the possible constructors of the lists of preferences of men inside the tuples:

\begin{code}
lengthPrefsExtLemma (man , prefs) [] n = z≤′n
lengthPrefsExtLemma (man , []) ((fst , []) ∷ ms) n = n≤′m+n n (lengthPrefs ms)
lengthPrefsExtLemma (man , x ∷ prefs)
                    ((fst , []) ∷ ms)
                    n = lengthPrefsExtLemma (man , x ∷ prefs) ms n
lengthPrefsExtLemma (man , [])
                    ((fst , w ∷ ws) ∷ ms)
                    n = n≤′m+n n (suc (lengthPrefs ((fst , ws) ∷ ms)))
lengthPrefsExtLemma (man , x ∷ prefs)
                    ((fst , w ∷ ws) ∷ ms)
                    n = m≤n+r+m (suc (length ws + lengthPrefs ms)) n (length prefs)

\end{code}

Let us attempt a more sophisticated proof. Since the sum of preference lists is calculated by summing up the preferences of free and engaged men, we can state that the sum is at most the same as the sum of preferences in each of the lists at the same time. In this case, our proofs will consist of pairs, constructed by the \_ , \_ operator. In Agda:

\begin{code}
lengthPrefsOneSide : ∀ (freeMen engagedMen : List (ℕ × List ℕ))(k : ℕ) →
                     k ≡ compSumPrefLists freeMen engagedMen →
                     (lengthPrefs freeMen ≤′ k) × (lengthPrefs engagedMen ≤′ k)

-- For empty preference lists, we use z≤′n to show that 0 ≤ n for all n. 
lengthPrefsOneSide [] [] k p = z≤′n , z≤′n

-- If the man at the head of the some list has an empty preference list,
-- we can only be sure the desired property holds by looking at the next one
lengthPrefsOneSide [] ((fst , []) ∷ engagedMen)
                   k p = z≤′n ,
                         proj₂ (lengthPrefsOneSide [] engagedMen k p)

-- Using reflexivity and symmetry
lengthPrefsOneSide [] ((fst , x ∷ snd) ∷ engagedMen)
                   k p = z≤′n , ≤⇒≤′ (≤-reflexive (sym p))

lengthPrefsOneSide ((fst , []) ∷ freeMen) []
                   k p = proj₁ (lengthPrefsOneSide freeMen [] k p) , z≤′n

-- Let us use some previously defined proofs!
lengthPrefsOneSide ((fst , x ∷ snd) ∷ freeMen)
                   [] k p = ≤⇒≤′
                            (≤-reflexive
                              (+-zero k (lengthPrefs ((fst , x ∷ snd) ∷ freeMen))
                              (+-move-zero (suc (lengthPrefs ((fst , snd) ∷ freeMen)))
                            k p)))
                            , z≤′n

lengthPrefsOneSide ((fst , []) ∷ freeMen)
                   ((fst₁ , []) ∷ engagedMen)
                   k p = lengthPrefsOneSide freeMen engagedMen k p

lengthPrefsOneSide ((fst , []) ∷ freeMen)
                   ((fst₁ , x ∷ snd₁) ∷ engagedMen)
                   .(lengthPrefs freeMen + suc (lengthPrefs ((fst₁ , snd₁) ∷ engagedMen)))
                   refl = proj₁ (lengthPrefsOneSide
                                   freeMen
                                   ((fst₁ , x ∷ snd₁) ∷ engagedMen)
                                   (lengthPrefs freeMen +
                                     suc (lengthPrefs ((fst₁ , snd₁) ∷ engagedMen))
                                   )
                                   refl) ,
                           ≤⇒≤′ (n≤m+n (lengthPrefs freeMen)
                                (suc (lengthPrefs ((fst₁ , snd₁) ∷ engagedMen))))
lengthPrefsOneSide ((fst , x ∷ snd) ∷ freeMen)
                   ((fst₁ , []) ∷ engagedMen)
                   .(suc (lengthPrefs ((fst , snd) ∷ freeMen) + lengthPrefs engagedMen))
                   refl = ≤⇒≤′
                          (s≤s
                            (n+m≤n+m+s
                              (lengthPrefs freeMen)
                              (length snd)
                              (lengthPrefs engagedMen))
                          )
                          ,
                          proj₂ (lengthPrefsOneSide
                                  ((fst , x ∷ snd) ∷ freeMen)
                                  engagedMen
                                  ((suc (lengthPrefs ((fst , snd) ∷ freeMen) +
                                    lengthPrefs engagedMen)))
                                  (cong suc refl))

lengthPrefsOneSide ((fst , x ∷ snd) ∷ freeMen)
                   ((fst₁ , x₁ ∷ snd₁) ∷ engagedMen)
                   p refl = n≤n+m
                              (suc (lengthPrefs ((fst₁ , snd₁) ∷ engagedMen)))
                              (suc (lengthPrefs ((fst , snd) ∷ freeMen)))
                            ,
                            ≤⇒≤′
                            (n≤m+n
                              (lengthPrefs ((fst , x ∷ snd) ∷ freeMen))
                              (lengthPrefs ((fst₁ , x₁ ∷ snd₁) ∷ engagedMen))
                            )

\end{code}

We hope that the previous examples showed how we can put together different pieces of proofs in order to achieve bigger results in Agda. It is worth noticing that many of these proofs can be defined in different ways; whenever possible we tried to use some properties already provided by Agda's standard library, but as we have seen, these can all be redefined at any time with some simple mathematical constructs (such as induction, recursion, congruency, symmetry, transitivity and so on).

Finally, we introduce an extra feature of Agda that precisely allows us to simplify some proofs. Agda constains a semiring solver for natural numbers, which allow us to prove some equalities by simply calling on a solver which reduces things to its normal form \cite{2018UsingSolver}.

\begin{code}
import Data.Nat.Solver
open Data.Nat.Solver.+-*-Solver
  using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)
\end{code}

Here an alternative language is imported for expressing the proof obligations we would like to fulfill: the := operator instead of =; the :+ and :* operators instead of their natural number counterparts; \texttt{con n} instead of n and so on.

We know the following equation to be true for any x natural number:

\begin{code}
lem : (x : ℕ) → (2 * (x + 4) ≡ 8 + 2 * x)
\end{code}

While expanding the definition application of natural numbers however, we end up with a huge goal in Agda: \textt{x + 4 + (x + 4 + 0) ≡ suc (suc (suc (suc (suc (suc (suc (suc (x + (x + 0)))))))))}. This definitely needs a lot of moving zeros and suc's around, but the ring solver allows for a cleaner definition.

The ring solver takes at least three parameters: how many variables are involved; what is the expression to be solved, written down in an alternative syntax; the refl axiom for wrapping the equality up. Then come the variables to replace the ones in the lambda, if any:
\begin{code}
lem = solve 1 (λ x' → con 2 :* (x' :+ con 4) := con 8 :+ con 2 :* x') refl
\end{code}

Now let us turn into the definition of the \texttt{stepDec} function. In order to make use of Agda's computational capabilities, We must pattern match on proofs about a function by pattern matching in the same way that function does. Let us look at each case individually:

\begin{itemize}
  \item When both the lists of free men and engaged men are empty, our proposition is true since calling the step function will not modify the value of $k$, the sum of preference lists (according to the definition of step). We can in turn prove that $k \le k$ from the definition of ≤′-refl.
  \item When the list of free men is empty but there is at least one man engaged, our proposition is true since calling the step function will not modify the value of $k$ either.
  \item When there is at least one free man but he has no woman to propose to (as pointed before, a dummy case), calling the step function will again not modify the value of $k$.
  \item When there is a free man who has a woman to propose to, we analyse if the woman has a partner or not.
    \begin{itemize}
      \item In case she does, we analyse if the new suitor is preferred to the current husband.
        \begin{itemize}
          \item In case he's not, we must give a proof that the sum of preference lists was decreased by one in this step (since the man discards the woman from the list).
          \item In case he is in fact accepted, we must write down a lemma which calls the functions involved and proves that after calling these functions, the value of $k$ will be equal or decreased. Again, this function should repeat the pattern matching of the involved functions.
        \end{itemize}
      \item In case she was single, she accepts the proposal immediately. We must write down a lemma which shows that, when that man moves from the list of free men to the list of engaged men, the value of $k$ is decreased.
    \end{itemize}
\end{itemize}

We first present the "single woman lemma", constructed with the help of Agda's semiring solver. This lemma is greatly simplified by the fact that the return of the step function for this case immediately discards the woman at the front of the preference list, so our proof obligation for this case is

\begin{code}
singleWomanLemma : ∀ freeMen n prefs engagedMen →
  lengthPrefs freeMen + lengthPrefs ((n , prefs) ∷ engagedMen) ≤′
  suc (lengthPrefs ((n , prefs) ∷ freeMen) + lengthPrefs engagedMen)
\end{code}

which is true at first glance, if you consider that the elements of the proposition found on the left-hand side are just rearranged on the right-hand side. One would then think that this can be proven with the help of some function that returns a proof that n $\le$ 1 + n; however it is not straight-forward to prove with simple mathematical constructs that the sum on the right-hand side and on the left-hand side are the same. At least, not without a semiring solver: 

\begin{code}

-- The definition of subst according to Agda's user manual:
-- subst : {A : Set} (C : A → Set) {x y : A} → x == y → C x → C y

singleWomanLemma freeMen
                 n
                 prefs
                 engagedMen = subst

                 -- We would like to prove something about y. 
                              (λ y → lengthPrefs freeMen +
                                     lengthPrefs ((n , prefs) ∷ engagedMen)
                                     ≤′ suc y)
                 -- We give a proof that x == y
                              (solve 3
                                     (λ x y z → x :+ (y :+ z) := y :+ x :+ z)
                                     refl
                                     (lengthPrefs freeMen)
                                     (length prefs)
                                     (lengthPrefs engagedMen)
                              )
                 -- And another one that the property holds just for x.
                              (≤⇒≤′ (n≤1+n _))
                 -- This function will return a proof that it holds for y!
\end{code}

For the case when a woman says yes to a proposal, thus dumping her current fiance and being paired to new one, we write another lemma in the hope to prove that the function applications involved preserve or decrease the sum of the preference lists. Many cases can be solved by using the semiring solver, since they involve some empty lists and we already know how to construct a (more convoluted proof) that n $\le$ n + 1. Later, however, we must effectively implement the proof of the cases that stem from the comparison of the new suitor to the current husband. Part of this implementation is given below: 

\begin{code}
lemmaProposeTrue : ∀ (freeMen engagedMen : List (ℕ × List ℕ))
                     (formerHusband man : ℕ)
                     (prefs : List ℕ) →
                   length (proj₂
                             (proj₂
                             (safeAddNewEngagedMan′ (man , prefs)
                                                     formerHusband
                                                     engagedMen))
                          ) +
                   lengthPrefs freeMen +
                   lengthPrefs (proj₁
                                 (safeAddNewEngagedMan′ (man , prefs)
                                                        formerHusband
                                                        engagedMen))
                   ≤′
                   suc (length prefs +
                        lengthPrefs freeMen +
                        lengthPrefs engagedMen)

lemmaProposeTrue freeMen [] formerHusband man prefs =
                              subst  (λ x → lengthPrefs freeMen +
                                            (length prefs + 0)
                                            ≤′ suc x)
                                (solve 2
                                       (λ x y → x :+ (y :+ con 0) := (y :+ x :+ con 0))
                                       refl
                                       (lengthPrefs freeMen)
                                       (length prefs)
                                )
                                (≤⇒≤′ (n≤1+n _))

lemmaProposeTrue freeMen ((m , prefsM) ∷ []) formerHusband man prefs
  with compare formerHusband m
lemmaProposeTrue freeMen
                 ((.(suc (formerHusband + k)) , prefsM) ∷ [])
                 formerHusband
                 man
                 prefs | less .formerHusband k =
                         subst
                           (λ x → lengthPrefs freeMen +
                                  (length prefs + (length prefsM + 0))
                             ≤′ suc x)
                           (solve 3
                             (λ x y z → x :+ (y :+ (z :+ con 0))
                                := y :+ x :+ (z :+ con 0))
                             refl
                             (lengthPrefs freeMen)
                             (length prefs)
                             (length prefsM))
                           (≤⇒≤′ (n≤1+n _))

lemmaProposeTrue freeMen ((m , prefsM) ∷ []) .m man prefs | equal .m =
                 subst
                   (λ x → length prefsM + lengthPrefs freeMen +
                          (length prefs + 0) ≤′ suc x)
                   (solve 3
                     (λ x y z → x :+ y :+ (z :+ con 0)
                       := z :+ y :+ (x :+ con 0))
                     refl
                     (length prefsM)
                     (lengthPrefs freeMen)
                     (length prefs)
                   )
                   (≤⇒≤′ (n≤1+n _))

lemmaProposeTrue freeMen
                 ((m , prefsM) ∷ [])
                 .(suc (m + k)) man prefs | greater .m k =
                 subst
                   (λ x → lengthPrefs freeMen +
                     (length prefs + (length prefsM + 0))
                     ≤′ suc x)
                   (solve 3
                          (λ x y z → x :+ (y :+ (z :+ con 0))
                            := y :+ x :+ (z :+ con 0))
                          refl
                          (lengthPrefs freeMen)
                          (length prefs)
                          (length prefsM)
                   )
                   (≤⇒≤′ (n≤1+n _))

lemmaProposeTrue freeMen
                 ((m , prefsM) ∷ ms ∷ engagedMen)
                 formerHusband
                 man
                 prefs with compare formerHusband m

lemmaProposeTrue freeMen
                 ((.(suc (formerHusband + k)) , prefsM) ∷ ms ∷ engagedMen)
                 formerHusband
                 man
                 prefs | less .formerHusband k
                       with safeAddNewEngagedMan′ (man , prefs)
                                                  formerHusband
                                                  (ms ∷ engagedMen)

-- This is yet to be proven, but if it is, our lemma is sound.
lemmaProposeTrue freeMen
                 ((.(suc (formerHusband + k)) , prefsM) ∷ ms ∷ engagedMen)
                 formerHusband
                 man
                 prefs | less .formerHusband k | updatedEngagedMen , extraInfo = {!!}

-- The equal case can, of course, be solved with the semiring solver.
lemmaProposeTrue freeMen
                 ((m , prefsM) ∷ ms ∷ engagedMen)
                 .m
                 man
                 prefs | equal .m =
                         subst
                           (λ x → length prefsM + lengthPrefs freeMen +
                                  (length prefs + (length (proj₂ ms) +
                                   lengthPrefs engagedMen))
                                  ≤′ suc x)
                           (solve 5
                                  (λ u v w y z →
                                    u :+ v :+ (w :+ (y :+ z))
                                    := w :+ v :+ (u :+ (y :+ z)))
                                  refl
                                  (length prefsM)
                                  (lengthPrefs freeMen)
                                  (length prefs)
                                  (length (proj₂ ms))
                                  (lengthPrefs engagedMen))
                           (≤⇒≤′ (n≤1+n _))

-- This is yet to be proven, but if it is, our lemma is sound.
lemmaProposeTrue freeMen ((m , prefsM) ∷ ms ∷ engagedMen) .(suc (m + k)) man prefs |
                         greater .m k = {!!}

\end{code}

With these different pieces in place we can write down the $stepDec$ function:

\begin{code}
stepDec (mkState men [] [] women couples k p) = ≤′-refl
stepDec (mkState men [] ((man , prefs) ∷ engagedMen) women couples k p) = ≤′-refl
stepDec (mkState men ((man , []) ∷ freeMen) engagedMen women couples k p) = ≤′-refl
stepDec (mkState men ((man , w ∷ prefs) ∷ freeMen) engagedMen women couples k p)
  with getPartner w couples
...             | just h with propose man h (getPreferenceList w women)
...             | true  = lemmaProposeTrue freeMen engagedMen h man prefs
...             | false = ≤⇒≤′ (n≤1+n _)
stepDec (mkState men ((n , w ∷ prefs) ∷ freeMen) engagedMen women couples k p)
  | nothing = singleWomanLemma freeMen n prefs engagedMen
\end{code}

\subsection{Correctness}

We now proceed to discuss the correctness of the deferred acceptance algorithm. Again, we start by giving some definitions and a few helper functions.

First we define the type of elements that belong to a list:

\begin{code}
data _∈_ {A : Set}(a : A) : List A → Set where
  now   : (as : List A) → a ∈ (a ∷ as)
  later : {a' : A}{as : List A} → a ∈ as → a ∈ (a' ∷ as)
\end{code}

Then since we defined the lookup functions on the preference lists with Maybe-types, we give a bigger-than comparison for Maybe ℕ-typed elements:

\begin{code}
data _>just_ : Maybe ℕ → Maybe ℕ → Set where
  _from>_ : {m n : ℕ} → m > n → just m >just just n
\end{code}

With that we can define a helper for the condition of stability: a person is better than another one in a preference list if it appears earlier in it.

\begin{code}
_≻[_]_ : ℕ → List ℕ → ℕ → Set
person ≻[ list ] person₂ = positionInList person₂ list >just positionInList person list
\end{code}

Given a man $m$ and a woman $w$ and their preferences, the condition of stability is satisfied if no other $m\prime$ and $w\prime$ are better positioned in their preference lists than their partners.

\begin{code}
conditionOfStabilitySatisfied : (c₁ : (ℕ × List ℕ) × (ℕ × List ℕ))
                                (c₂ : (ℕ × List ℕ) × (ℕ × List ℕ))
                                → Set
conditionOfStabilitySatisfied ((m , prefsM) , w , prefsW) ((m' , prefsM') , w' , prefsW') =
  (¬ ( ( w' ≻[ prefsM ] w ) ×  ( m ≻[ prefsW' ] m' )))
  ×
  (¬ ( (w ≻[ prefsM' ] w') × (m' ≻[ prefsW ] m)))
\end{code}

We are ready to write down a definition of stable matching: a matching is stable if no man are waiting to be married and the condition of stability is satisfied for every two pairs of man and woman formed.

\begin{code}
is-stable-matching : MatchingState → Set
is-stable-matching (mkState men freeMen engagedMen women couples k p) =
  (freeMen ≡ []) × (
      (c₁ c₂ : ℕ × ℕ) → c₁ ∈ couples → c₂ ∈ couples → ¬ (c₁ ≡ c₂) → 
          conditionOfStabilitySatisfied
          ( ( (proj₁ c₁) , getPreferenceList (proj₁ c₁) men) ,
            ( (proj₂ c₁) , getPreferenceList (proj₂ c₁) women))
          ( ( (proj₁ c₂) , getPreferenceList (proj₁ c₂) men) ,
            ( (proj₂ c₂) , getPreferenceList (proj₂ c₂) women)))
\end{code}

Now, let us examine some examples to make use of these definitions. We look at the two cases from Gale and Shapley's original paper, one where we have an uncomplicated setup for which the deferred acceptance algorithm gives every man the first possible choice of woman, and another where there is in fact only one possible stable set of marriages and the algorithm takes a longer number of steps to arrive to its final state.

\begin{code}
-- List of preferences of men and women from the
-- Gale-Shapley canonical example
listMen : List (ℕ × List ℕ)
listMen = (1 , ( 1 ∷ 2 ∷ 3 ∷ [] )) ∷ (2 , ( 2 ∷ 3 ∷ 1 ∷ [])) ∷ (3 , ( 3 ∷ 1 ∷ 2 ∷ [])) ∷ []

listWomen : List (ℕ × List ℕ)
listWomen = (1 , ( 2 ∷ 3 ∷ 1 ∷ [] )) ∷ (2 , ( 3 ∷ 1 ∷ 2 ∷ [])) ∷ ((3 , ( 1 ∷ 2 ∷ 3 ∷ []))) ∷ []

-- Extra example : men and women have only
-- one possible stable set of marriages!
-- What could happen...?
listDifficultMen : List (ℕ × List ℕ)
listDifficultMen = (1 , ( 1 ∷ 2 ∷ 3 ∷ 4 ∷ [] )) ∷
                   (2 , ( 1 ∷ 4 ∷ 3 ∷ 2 ∷ [] )) ∷
                   (3 , ( 2 ∷ 1 ∷ 3 ∷ 4 ∷ [] )) ∷
                   (4 , ( 4 ∷ 2 ∷ 3 ∷ 1 ∷ [] )) ∷ []

listDifficultWomen : List (ℕ × List ℕ)
listDifficultWomen = (1 , ( 4 ∷ 3 ∷ 1 ∷ 2 ∷ [] )) ∷
                     (2 , ( 2 ∷ 4 ∷ 1 ∷ 3 ∷ [] )) ∷
                     (3 , ( 4 ∷ 1 ∷ 2 ∷ 3 ∷ [] )) ∷
                     (4 , ( 3 ∷ 2 ∷ 1 ∷ 4 ∷ [] )) ∷ []
\end{code}

We can check that our implementation reaches the result promised by Gale and Shapley by simply constructing the proof that some applications of the step function reach the expected end state:

\begin{code}
exStart exEnd exEndExpected : MatchingState
exStart = mkState listMen listMen [] listWomen [] 9 refl
\end{code}

Gale and Shapley tell us that, for the first simple example, each men gets his first woman from the list as a wife and there are no conflicts amongst them. So we expect the following end state:
\begin{code}
exEndExpected = mkState listMen
                        []
                        ((3 , (1 ∷ 2 ∷ [])) ∷
                         ((2 , 3 ∷ 1 ∷ []) ∷
                          (1 , 2 ∷ 3 ∷ []) ∷ [] ))
                        listWomen
                        ((2 , 2) ∷ (3 , 3) ∷ (1 , 1) ∷ [])
                        6
                        refl
exEnd         = step (step (step (step exStart)))
\end{code}

Which we can see is what we get:

\begin{code}
resultIsWhatWeExpected : exEnd ≡ exEndExpected
resultIsWhatWeExpected = refl
\end{code}

The same goes for the second, harder example:

\begin{code}
ex2Start ex2End ex2EndExpected : MatchingState
ex2Start = mkState listDifficultMen listDifficultMen [] listDifficultWomen [] 16 refl

ex2EndExpected = mkState listDifficultMen
                           []
                           ((1 , ( 4 ∷ [] )) ∷ (4 , (3 ∷ 1 ∷ [])) ∷
                             (2 , ( 3 ∷ 2 ∷ [] )) ∷ (3 , ( 3 ∷ 4 ∷ [])) ∷ [])
                           listDifficultWomen
                           (((2 , 4) ∷ (4 , 2) ∷ (1 , 3) ∷ (3 , 1) ∷ []))
                           7
                           refl

ex2End  = step (step (step (step (step
               (step (step (step (step ex2Start))))))))

result2IsWhatWeExpected : ex2End ≡ ex2EndExpected
result2IsWhatWeExpected = refl

\end{code}

Expectably, these consecutive \texttt{step} applications are precisely the total applications of step if we utilize our previously defined \texttt{allSteps} function:

\begin{code}
numberOfStepsIsCorrect : exEnd ≡ allSteps exStart
numberOfStepsIsCorrect = refl

numberOfStepsIsCorrectAgain : ex2End ≡ allSteps ex2Start
numberOfStepsIsCorrectAgain = refl
\end{code}

Expressing such properties in the code also calls our attention to later inconsistencies during coding: in case we do some modification that breaks the step function, the type checking will fail for these small proofs of equality as if a test failed. Here, we are still on the same level as a unit tester running a test suite in their code, but we will soon take the leap to the next one.

What about showing that the matching returned by the deferred acceptance algorithm is stable? Let's do it for \texttt{exEnd}:

\begin{code}
matchIsStableHelper : (c₁ c₂ : ℕ × ℕ)  →
      -- Given any two couples in exEnd
      c₁ ∈ MatchingState.couples exEnd →
      c₂ ∈ MatchingState.couples exEnd →
      -- If it's not the same couple
      ¬ (c₁ ≡ c₂) →
      -- Then the condition of stability is satisfied for them 
       conditionOfStabilitySatisfied
      (((proj₁ c₁) ,
      (getPreferenceList (proj₁ c₁) (MatchingState.men exEnd))) ,
      ((proj₂ c₁) ,
      (getPreferenceList (proj₂ c₁) (MatchingState.women exEnd))))
      (((proj₁ c₂) ,
      (getPreferenceList (proj₁ c₂) (MatchingState.men exEnd))) ,
      ((proj₂ c₂) ,
      (getPreferenceList (proj₂ c₂) (MatchingState.women exEnd))))
\end{code}

The proof for a particular case can be done by exhaustive pattern matching on the constructors of the elements; in particular, we pattern match on the proofs that the couples are part of the list of couples. There are three different possibilities for this pattern matching:

\begin{itemize}
  \item We are looking at the case where $c_1$ and $c_2$ are in fact the same couple: we use the proof that $\neg (c_1 \== c_2)$ to eliminate this impossible case.
  \item The pattern is simply not possible (the combinations with less than 2 couples), so we write them out as absurd patterns. 
  \item We are looking at two different couples indeed, and must provide a proof that at least one person prefers their partner to the possibility in the other couple (since the condition of stability is written down as a pair, or cartesian product, only one suffices). Since our comparison helper function for persons in preference lists, $\succ$, is total and the preference list search function only maybe returns an element, we use our helper \texttt{>from>} constructor that compares Maybe-N typed elements to show that this is true for the side of the men in every one of these cases,\footnote{Remember every man gets the best possible wife, so surely his wife is preferred to any alternative.} and the second part of the proof can be skipped with an underline marker since it is sufficient for the condition of stability that at least one side fullfills it.
\end{itemize}

\begin{code}
matchIsStableHelper _ _ (now .((3 , 3) ∷ (1 , 1) ∷ []))
                        (now .((3 , 3) ∷ (1 , 1) ∷ []))
                        p = ⊥-elim (p refl) , ⊥-elim (p refl)
matchIsStableHelper _ _ (now .((3 , 3) ∷ (1 , 1) ∷ []))
                        (later (now .((1 , 1) ∷ [])))
                        p = (λ { (_from>_ () , _) }) ,
                             λ { (_from>_ () , _) }
matchIsStableHelper _ _ (now .((3 , 3) ∷ (1 , 1) ∷ []))
                        (later (later (now .[])))
                        p = (λ { (_from>_ () , _) }) ,
                             λ { (_from>_ () , _) }
matchIsStableHelper _ _ (now .((3 , 3) ∷ (1 , 1) ∷ []))
                        (later (later (later ())))
                        p
matchIsStableHelper _ _ (later (now .((1 , 1) ∷ [])))
                        (now .((3 , 3) ∷ (1 , 1) ∷ []))
                        p = (λ { (_from>_ () , _) }) ,
                             λ { (_from>_ () , _) }
matchIsStableHelper _ _ (later (now .((1 , 1) ∷ [])))
                        (later (now .((1 , 1) ∷ [])))
                        p = ⊥-elim (p refl)
matchIsStableHelper _ _ (later (now .((1 , 1) ∷ [])))
                        (later (later (now .[])))
                        p = (λ { (_from>_ () , _) }) ,
                             λ { (_from>_ () , _) }
matchIsStableHelper _ _ (later (now .((1 , 1) ∷ [])))
                        (later (later (later ())))
matchIsStableHelper _ _ (later (later (now .[])))
                        (now .((3 , 3) ∷ (1 , 1) ∷ []))
                        p = (λ { (_from>_ () , _) }) ,
                             λ { (_from>_ () , _) }
matchIsStableHelper _ _ (later (later (now .[])))
                        (later (now .((1 , 1) ∷ [])))
                        p = (λ { (_from>_ () , _) }) ,
                             λ { (_from>_ () , _) }
matchIsStableHelper _ _ (later (later (now .[])))
                        (later (later (now .[])))
                        p = ⊥-elim (p refl)
matchIsStableHelper _ _ (later (later (now .[])))
                        (later (later (later ())))
matchIsStableHelper _ _ (later (later (later ()))) _ _
\end{code}

So, again, what does it mean for a matching to be stable according to our definition? To have an empty list of free men... which we can prove for \texttt{exEnd} using the refl axiom; and to satisfy the condition of stability for every two couples... which is the definition we have just provided of \texttt{matchIsStableHelper}. We can then give a proof that \texttt{exEnd} is indeed a stable matching: 

\begin{code}
matchIsStable : is-stable-matching exEnd
matchIsStable = refl , matchIsStableHelper
\end{code}

Let us now take that promised leap onto the next level. We postulate that, indeed, any matching returned by the Gale-Shapley algorithm is stable:

\begin{code}
postulate
  pAnyMatchIsStable : ∀ (m m′ : MatchingState) →
                   m′ ≡ allSteps m →
                   MatchingState.freeMen m′ ≡ [] →
                   is-stable-matching m′
\end{code}

We can go about trying to prove it by providing similar elements to the ones used in the proof of the particular case before (the proof is incomplete, but the given pattern matching is a good start):

\begin{code}
anyMatchIsStableHelper : ∀ (m : MatchingState) → (MatchingState.freeMen m ≡ []) →
      (c₁ c₂ : ℕ × ℕ)  →
      -- Given any two couples in a matching
      c₁ ∈ MatchingState.couples m →
      c₂ ∈ MatchingState.couples m →
      -- If it's not the same couple
      ¬ (c₁ ≡ c₂) →
      -- Then the condition of stability is satisfied 
       conditionOfStabilitySatisfied
      (((proj₁ c₁) ,
      (getPreferenceList (proj₁ c₁) (MatchingState.men m))) ,
      ((proj₂ c₁) ,
      (getPreferenceList (proj₂ c₁) (MatchingState.women m))))
      (((proj₁ c₂) ,
      (getPreferenceList (proj₁ c₂) (MatchingState.men m))) ,
      ((proj₂ c₂) ,
      (getPreferenceList (proj₂ c₂) (MatchingState.women m))))
\end{code}

The first pattern is absurd: if there are no couples at all we can't possibly think about this!

\begin{code}
anyMatchIsStableHelper (mkState _ [] _ _ [] _ _)
                       p₁ (fst , snd) (fst₁ , snd₁) () p₂ p₃
\end{code}

What interests us is the case when there are no more free men and at least one couple has been formed:

\begin{code}
anyMatchIsStableHelper (mkState men [] engagedMen women (x ∷ couples)
                                sumPrefLists sumEq)
                       refl (fst , snd) (fst₁ , snd₁) p₁ p₂ p₃ = {!!} , {!!}
\end{code}

Another absurd pattern which is cancelled out by Agda in this suggested version is the one where there are still some free men:

\begin{code}
anyMatchIsStableHelper (mkState _ (m ∷ freeMen) _ _ _ _ _)
                       () c₁ c₂ p₂ p₃ p₄

\end{code}

With the helper proof we can then prove the match is stable 

\begin{code}
anyMatchIsStable : ∀ (m m′ : MatchingState) →
                   m′ ≡ allSteps m →
                   MatchingState.freeMen m′ ≡ [] →
                   is-stable-matching m′
anyMatchIsStable m m′ p₁ p₂ = p₂ , {!!}
\end{code}

\subsection{Optimality}

We have logically reasoned in Section \ref{output-is-optimal} that, given every possible stable matching, no man has a better option than the woman he is assigned to by the Gale-Shapley algorithm. In Agda:

\begin{code}
-- In order to define that a matching m₁ is better than a matching m₂,
-- we take into consideration that for all men they get a better
-- (earlier in their list) wife in m₁ than in m₂; this can be seen
-- from the size of his preference list in the final state of matching. 
is-better-matching : (m₁ m₂ : MatchingState) → Set
is-better-matching (mkState men freeMen engagedMen women couples k p)
                   (mkState men₁ freeMen₁ engagedMen₁ women₁ couples₁ k₁ p₁) =
                   is-stable-matching
                     (mkState men freeMen engagedMen women couples k p) ×
                   is-stable-matching
                     (mkState men₁ freeMen₁ engagedMen₁ women₁ couples₁ k₁ p₁) ×
                   ((m₁ m₂ : ℕ × List ℕ) →
                   m₁ ∈ engagedMen →  m₂ ∈ engagedMen₁ →
                   proj₁ m₁ ≡ proj₁ m₂ →
                   getPreferenceList (proj₁ m₁) men
                   ≡ getPreferenceList (proj₁ m₂) men₁ →
                   length (proj₂ m₁) ≥ length (proj₂ m₂))

\end{code}

Let us define another possible stable matching from the first example given by Gale and Shapley:

\begin{code}
-- Let us demonstrate with the first canonical example. Gale and Shapley
-- tell us that another possible stable marriage (not returned by their
-- algorithm) is obtained by giving every woman her first choice:
anotherPossibleStableMatching : MatchingState
anotherPossibleStableMatching = mkState listMen
                                        []
                                        ((3 , []) ∷ (1 , []) ∷ (2 , []) ∷ [])
                                        listWomen
                                        ((3 , 2) ∷ (1 , 3) ∷ (2 , 1) ∷ [])
                                        _
                                        refl
\end{code}

We go about proving it as we have seen before:

\begin{code}
anotherMatchIsStableHelper : (c₁ c₂ : ℕ × ℕ) →
      c₁ ∈ MatchingState.couples anotherPossibleStableMatching →
      c₂ ∈ MatchingState.couples anotherPossibleStableMatching →
      ¬ c₁ ≡ c₂ →
      conditionOfStabilitySatisfied
      (((proj₁ c₁) ,
      (getPreferenceList (proj₁ c₁) (MatchingState.men anotherPossibleStableMatching))) ,
      ((proj₂ c₁) ,
      (getPreferenceList (proj₂ c₁) (MatchingState.women anotherPossibleStableMatching))))
      (((proj₁ c₂) ,
      (getPreferenceList (proj₁ c₂) (MatchingState.men anotherPossibleStableMatching))) ,
      ((proj₂ c₂) ,
      (getPreferenceList (proj₂ c₂) (MatchingState.women anotherPossibleStableMatching))))
anotherMatchIsStableHelper _ _ (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               p = ⊥-elim (p refl)
anotherMatchIsStableHelper _ _ (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               (later (now .((2 , 1) ∷ [])))
                               p = (λ { (_ , _from>_ ()) }) ,
                                    λ { (_ , _from>_ ()) }
anotherMatchIsStableHelper _ _ (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               (later (later (now .[])))
                               p = (λ { (_ , _from>_ ()) }) ,
                                    λ { (_ , _from>_ ()) }
anotherMatchIsStableHelper _ _ (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               (later (later (later ())))
                               p
\end{code}

Further cases are omitted for the sake of brevity, as it works exactly as the $matchIsStableHelper$ function discussed before.

\begin{code}[hide]
anotherMatchIsStableHelper _ _ (later (now .((2 , 1) ∷ [])))
                               (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               p = (λ { (_ , _from>_ ()) }) ,
                                    λ { (_ , _from>_ ()) } 
anotherMatchIsStableHelper _ _ (later (later (now .[])))
                               (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               p = (λ { (_ , _from>_ ()) }) ,
                                    λ { (_ , _from>_ ()) }
anotherMatchIsStableHelper _ _ (later (later (later ())))
                               (now .((1 , 3) ∷ (2 , 1) ∷ []))
                               p
anotherMatchIsStableHelper _ _ (later (now .((2 , 1) ∷ [])))
                               (later (now .((2 , 1) ∷ [])))
                               p = ⊥-elim (p refl)
anotherMatchIsStableHelper _ _ (later (now .((2 , 1) ∷ [])))
                               (later (later (now .[])))
                               p = (λ { (_ , _from>_ ()) }) ,
                                    λ { (_ , _from>_ ()) }
anotherMatchIsStableHelper _ _ (later (now .((2 , 1) ∷ [])))
                               (later (later (later ())))
                               p
anotherMatchIsStableHelper _ _ (later (later (now .[])))
                               (later (now .((2 , 1) ∷ [])))
                               p = (λ { (_ , _from>_ ()) }) ,
                                    λ { (_ , _from>_ ()) }
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
\end{code}

We are then able to give a proof that this second matching is also stable, but that it is not better than the first one, also by exhaustive pattern matching:

\begin{code}
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

\end{code}

We postulate that a proof can be written for any stable matching in the same vein as the example above: 

\begin{code}
-- Given two stable matchings m₁ , m₂
-- where m₁ is the result of the computation of
-- the Gale-Shapley algorithm
-- and m₂ is a matching over the same man and women,
-- m₂ is at most as good as m₁ but no better.
postulate
  pAnyMatchIsBetter : ∀ (m m₁ m₂ : MatchingState) →
                     allSteps m ≡ m₁ →
                     MatchingState.men m₂ ≡ MatchingState.men m →
                     MatchingState.women m₂ ≡ MatchingState.women m →
                     is-stable-matching m₁ → is-stable-matching m₂ →
                     is-better-matching m₁ m₂

\end{code}}
