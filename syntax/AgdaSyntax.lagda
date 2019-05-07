\newcommand{\AgdaSyntax}{%

A data type $D$ can be defined by giving (zero or more) constructors, that is, functions returning an element of that data type. The classical example is the type of natural numbers:

\begin{code}
data Nat : Set where
    zero : Nat
    suc  : Nat → Nat
\end{code}

Any data type with zero constructors, i.e., empty type, will represent the trivially false proposition (conventionally called "bottom"). Since there are no constructors for it, it can only be eliminated, but not constructed at all:

\begin{code}
data False : Set where
\end{code}

The unit type is that which has one constructor (conventionally called "top"). It cannot be eliminated, just introduced:

\begin{code}
data ⊤ : Set where
  tt : ⊤
\end{code}

Since Agda presents support for dependent data types, we can also construct parameterized data types, such as the types of vectors with fixed size (note this construction can not be properly done, for example, in Haskell):

\begin{code}
data Vector (A : Set) : Nat → Set where
  []  : Vector A zero
  _∷_ : {n : Nat} → A → Vector A n → Vector A (suc n)
\end{code}

The type $Set$ represents the \emph{type of types} in Agda. That poses a direct problem since, per Russel's paradox, the collection of all sets is not a set \cite{2019Official2.5.4.2}; however it is important to have the possibility of defining a $Set : Set$.

In order to circumvent the paradox, Agda introduces universe levels: it says that the right-hand side type is a \emph{larger set} than the one on the left-hand side and only allows writing such expressions as $Set : Set₁$. With the power of dependent types and the special type $Level$, it also gives us the possibility of defining functions for any universe level:

\begin{code}
open import Agda.Primitive

data List {n : Level} (A : Set n) : Set n where
  []   : List A
  _::_ : A → List A → List A
\end{code}

These elements are sufficient for us to define the ideas discussed by Per Martin-Löf in \cite{Martin-Lof1980IntuitionisticTheory} and \cite{Martin-Lof1982ConstructiveProgramming}, for example\footnote{In reality, many of these elements are already defined in reusable, tried-and-true and sophisticated ways in Agda's builtin modules or in Agda's standard library; we merely want to give the reader an idea of how these pieces come to life from the language's basic building blocks.}:

\begin{code}
-- The definition of equality for elements of a certain same set.
-- For any universe level i,
-- for a type A in that universe level,
-- it takes two elements of A,
-- and returns a proof that a ≡ a 
data _≡_ {i : Level}{A : Set i} : A → A → Set i where
  refl  : (a : A) → a ≡ a
\end{code}

\begin{code}
-- Cartesian product (or record).
-- It will only work in the same universe level.
data _×_ {i : Level}(A : Set i)(B : Set i) : Set i where
  -- To create an element of type A AND B
  -- I must first give an A and then a B
  _,_   : A → B → A × B

-- Disjunct union
-- Notice that the sets can be in different universe levels;
-- the corresponding constructed type will be in a universe
-- maximum the sum of both
data _⊎_ {a b : Level}(A : Set a)(B : Set b) : Set (a ⊔ b) where
  -- If I have an element of type A
  -- I can return one of type A OR B 
  inj₁ : (x : A) → A ⊎ B
  -- If I have an element of type B too!
  inj₂ : (y : B) → A ⊎ B
\end{code}

It can be seen that our code is indeed very close to the mathematical expressions we have previously noted as conterpart to general programming constructs, and furthermore, having them written down gives us access to the elements of Agda as a functional programming language such as type-checking, lazy evaluation and other concepts which permeate modern type theory and its theorical base. How we enjoy the computational power of the language will be further discussed in Chapter \ref{Chapter4} as we write down the Gale-Shapley algorithm in Agda.
}
