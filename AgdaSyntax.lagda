\newcommand{AgdaSyntax}{%

A data type $D$ can be defined by giving (zero or more) constructors, that is, functions returning an element of that data type. The classical example is the type of natural numbers:

\begin{code}
data Nat : Set where
    zero : Nat
    suc  : Nat → Nat
\end{code}

Any data type with zero constructors will represent the trivially false proposition:

\begin{code}
data False : Set where
\end{code}

Since Agda presents support for dependent data types, we can also construct parameterized data types, such as the types of vectors with fixed size (note this construction can not be properly done, for example, in Haskell):

\begin{code}
data Vector (A : Set) : Nat → Set where
  []  : Vector A zero
  _∷_ : {n : Nat} → A → Vector A n → Vector A (suc n)
\end{code}

The type $Set$ represents the \emph{type of types} in Agda. That poses a direct problem since, per Russel's paradox TODO CITE, the collection of all sets is not a set; however it is important to have the possibility of defining a $Set : Set$.

In order to circumvent the paradox, Agda introduces universe levels: it says that the right-hand side type is a \emph{larger set} than the one on the left-hand side and only allows writing such expressions as $Set : Set₁$. With the power of dependent types and the special type $Level$, it also gives us the possibility of defining functions for any universe level:

\begin{code}
open import Agda.Primitive

data List {n : Level} (A : Set n) : Set n where
  []   : List A
  _::_ : A → List A → List A
\end{code}}
