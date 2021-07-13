\begin{code}[hide]
module _ where

variable A : Set

open import Data.Bool.Base using (Bool; true; false)
open import Function using (case_of_)

module Basics where
\end{code}
\section{Background} \label{sec:background}
Agda is an implementation of Martin-L{\"o}f's dependent type
theory~\cite{Martin-Lof-1972} extended with many constructions such as
records, modules, do-notation, \etc{}
We start with a brief overview of key Agda constructions that
are used in this paper.  We also present relevant parts of the
reflection API.  For a more in-depth introduction to Agda refer
to the Agda user manual~\cite{agda}.

\paragraph{Datatypes} Datatypes are defined as follows:
\begin{code}
  data ℕ : Set where
    zero  : ℕ
    suc   : ℕ → ℕ
\end{code}
The type \AD{ℕ} of unary natural numbers is a datatype with two constructors:
\AC{zero} and \AC{suc}.  Note that \AD{ℕ} itself belongs to
the type \AF{Set}, Agda's builtin type of all (small) types.

Agda allows the declaration of indexed
datatypes\footnote{\url{https://agda.readthedocs.io/en/v2.6.2/language/data-types.html}},
such as the type \AD{Vec} which is indexed over values of type \AD{ℕ}:
\begin{code}
  data Vec (A : Set) : ℕ → Set where
    []   : Vec A zero
    _∷_  : {n : ℕ} → A → Vec A n → Vec A (suc n)
\end{code}
The type \AD{Vec} \AB{A} \AB{n} represents vectors holding \AB{n}
values of type \AB{A}.  It has two constructors: \AC{[]} for the empty
vector of length \AC{zero} and \AC{\_∷\_} for adding an element to a
vector, increasing the length by 1.  Curly braces indicate hidden
arguments, which can be left out at function
applications.\footnote{\url{https://agda.readthedocs.io/en/v2.6.2/language/implicit-arguments.html}}
%Hidden arguments can be passed explicitly using the syntax \AC{\_∷\_}
%\{\AB{n}\} \AB{x} \AB{xs}.
The underscores in the name of \AC{\_∷\_}
indicate mixfix
syntax:\footnote{\url{https://agda.readthedocs.io/en/v2.6.2/language/mixfix-operators.html}}
we can write \AB{x} \AC{∷} \AB{xs} instead of \AC{\_∷\_} \AB{x}
\AB{xs}.

\paragraph{Pattern matching} Functions are defined in a pattern-matching style:
\begin{code}
  _+_ : ℕ → ℕ → ℕ
  zero     + y = y
  (suc x)  + y = suc (x + y)

  tail : {n : ℕ} → Vec ℕ (suc n) → Vec ℕ n
  tail (x ∷ xs) = xs
\end{code}
Agda requires that all definitions by pattern matching cover all
cases.  In the definition of \AF{tail}, we can omit the case for the
empty vector \AC{[]} because it takes an input of type \AD{Vec} \AB{A}
(\AC{suc}\ \AB{n}), so it can never be called with input \AC{[]}.

We can do a local case analysis on a value by
using the function \AF{case\_of\_} together with a
pattern-matching
lambda\footnote{\url{https://agda.readthedocs.io/en/v2.6.2/language/lambda-abstraction.html}}:
\begin{code}
  not : Bool → Bool
  not b = case b of λ where
    true   → false
    false  → true
\end{code}

\paragraph{Termination checking}
In order to ensure totality, Agda checks that all recursive functions
are terminating on all
inputs.\footnote{\url{https://agda.readthedocs.io/en/v2.6.2/language/termination-checking.html}}
%
While it is impossible to infer termination for an arbitrary function
due to the halting problem, Agda uses heuristics to handle common
cases.  The main idea behind the check is that the argument to the
recursive call has to be structurally smaller than the input argument.
This means that we have to remove at least one constructor from at
least one argument.  For example, in the recursive call to \AF{\_+\_},
the first argument is \AB{x}, which is structurally smaller than the
input \AC{suc} \AB{x}.

\paragraph{Proving equalities}
Agda can be used both as a programming language and a proof assistant.
One very common example of this is the equality type \AF{\_≡\_}, which
expresses equality of its two arguments. It has a single constructor
\AC{refl} : \AB{x} \AD{≡} \AB{x} stating that any value \AB{x} is
equal to itself.
\begin{code}[hide]
module Proving where
  open import Agda.Builtin.Nat renaming (Nat to ℕ)
  open import Data.Vec.Base
  open import Agda.Builtin.Equality
\end{code}
Using the equality type, we can state and prove equations between Agda
expressions, which are then checked by the typechecker. For example,
we can prove that \AN{1} \AF{+} \AN{1} = \AN{2}:
\begin{code}
  simple-proof : 1 + 1 ≡ 2
  simple-proof = refl
\end{code}
Although in this paper we only prove a few basic properties, the fact
that it is possible to prove arbitrary (functional) properties of
programs embedded in Agda is an important benefit of our approach.

%The definition of \AF{abs} uses the \emph{absurd pattern} (),
%indicating an impossible case for the first argument, \ie{} there is
%no constructor constructing a term of type \AD{Fin} \AC{zero}.
%Clauses with absurd patterns do not have a body, as the type system
%guarantees that they are never called at run-time.
%
%In the definition of \AF{wth} we demonstrate the use of the \AK{with}
%construction~\cite{10.1017/S0956796803004829} which makes it possible
%to match on the result of an expression locally.

% \todo[inline]{Amongst other things we need to explain with-clauses
%   and pattern-matching functions.  Maybe records and their eta-equality.
%
%   Nat, Fin, Vec, Eq, with, patterns, hidden values, mixfix}

\paragraph{Run-time irrelevance}

Function arguments can be marked as \emph{run-time
irrelevant}~\cite{McBride16} with the @0
annotation.\footnote{\url{https://agda.readthedocs.io/en/v2.6.2/language/runtime-irrelevance.html}} The
Agda typechecker guarantees that run-time irrelevant arguments are not
needed for evaluation of the program, they can thus safely be erased
by the compiler. For example, we can mark the \AB{n} argument to the
\AF{tail} function as run-time irrelevant:
\begin{code}
  tail' : {@0 n : ℕ} → Vec ℕ (suc n) → Vec ℕ n
  tail' (x ∷ xs) = xs
\end{code}
In our embedding of PostScript into Agda, we make use of this
annotation to ensure that the functions we define do not
computationally depend on arguments that are not on the stack and can
hence safely be erased during extraction of PostScript code (see
\secref{embedding} and \secref{extraction}).

\paragraph{Generalizable variables} To avoid having to bind implicit
arguments in type signatures, we make use of \emph{generalizable
variables}:\footnote{\url{https://agda.readthedocs.io/en/v2.6.2/language/generalization-of-declared-variables.html}}
\begin{code}
  variable
    X Y Z : Set
    @0 k l m n : ℕ
\end{code}
This allows us for example to skip the binding of \AB{n} in the type of \AF{tail}:
\begin{code}
  tail'' : Vec ℕ (suc n) → Vec ℕ n
  tail'' (x ∷ xs) = xs
\end{code}



\paragraph{Reflection}

The reflection API of Agda allows quoting and unquoting of expressions
and declarations, and provides access to some of the internals of the
Agda typechecker such as unification and
normalisation.\footnote{\url{https://agda.readthedocs.io/en/v2.6.2/language/reflection.html}}

Expressions are represented by a constructor such as \AC{con} (for
constructors), \AC{def} (for other defined symbols), or \AC{var} (for
variables) applied to a quoted name and a list of arguments.
\AC{vArg} denotes a visible argument, while \AC{hArg} is used for
hidden arguments).  For example, the full reflected form of the
expression \AC{zero} is \AC{con} (\AK{quote} \AC{zero}) \AC{[]}.

To make reflected syntax more readable, we use \emph{pattern synonyms}
for commonly used pieces of syntax. As a convention, the names of
these pattern synonyms start with a backtick \` followed by the name
of the represented Agda construct, for example:

\begin{code}[hide]
module FunExample where
  open import Data.List
  open import Data.Nat
  open import Data.Fin using (Fin)
  open import Data.Bool
  open import Reflection
  open import Data.Unit
  open import Data.Product
  open Clause
  open Pattern
\end{code}
\begin{code}
  pattern `ℕ        = def (quote ℕ) []
  pattern `zero     = con (quote zero) []
  pattern `suc x    = con (quote suc) (vArg x ∷ [])
  pattern _`+_ x y  = def (quote _+_) (vArg x ∷ vArg y ∷ [])
\end{code}

As a complete example, below is the definition of a function \AF{foo}
and its reflected syntax \AF{`foo}:

\begin{mathpar}
\codeblock{\begin{code}
  foo : ℕ → ℕ
  foo 0        = zero
  foo (suc x)  = x + x
\end{code}}
\and
\codeblock{\begin{code}
  `foo = function
    ( clause [] (vArg `zero ∷ []) `zero
    ∷ clause (("x" , vArg `ℕ) ∷ [])
             (vArg (`suc (var 0)) ∷ [])
             (var 0 [] `+ var 0 [])
    ∷ [] )
\end{code}}
\end{mathpar}


The reflected syntax of \AF{foo} is represented by the constructor \AC{function} applied to a list
of clauses. Each clause itself is represented by the constructor
\AC{clause} applied to three arguments: i) the telescope, which is a
list of the names of variables and their types; ii) the list of
 patterns; and iii) the body of the clause.
%
%The first clause does not have variables, so the telescope
%is empty. The second clause has one variable called \AB{x}.  The
%pattern list in the first clause has one argument.
%The actual pattern matches against the \AC{zero} constructor.
%
Variables (both in patterns and in terms) are given as de Bruijn indices
relative to the telescope of the clause.  That is, in the second clause the
de Bruijn index \AN{0} refers to the variable \AB{x}.  Note that we write
\AN{0} instead of \AC{zero}, as numbers are expanded
into their corresponding \AC{zero}/\AC{suc} representations.


\paragraph{The \AD{TC} monad}

Following the approach of \emph{elaborator reflection} introduced by
Idris~\cite{idris-refl}, Agda exposes many parts of the elaborator to
the reflection API, including reduction and normalisation of
expressions, through the \AD{TC} monad. Agda terms can be converted to
reflected syntax by using the \AF{quoteTC} primitive.

Functions of return type \AD{Term} → \AD{TC} \AD{⊤} can be marked as a
\AK{macro}. When the elaborator encounters a macro call, it runs the macro
and replaces it with the result.
\begin{comment}
For example, the macro \AF{norm} below takes a term, quotes it,
normalises the quoted term, and unifies the result with the hole.
%
Effectively, this macro is a partial evaluator for Agda programs.  For
example, \AF{norm} (\AN{1} \AF{+} \AN{1}) will be statically replaced
by \AN{2}.

\begin{code}
  macro norm : A → (Term → TC ⊤)
        norm x hole = do
          `x ← quoteTC x
          `x ← normalise `x
          unify `x hole
  test = norm (1 + 1) -- equivalent to 'test = 2'
\end{code}
\end{comment}
A macro can perform arbitrary manipulations on the syntactic structure
of Agda expressions as well as information obtained through operations
in the \AF{TC} monad.



% \begin{code}[hide]
%  module TermLang where
%   open import Data.List
%   open import Data.Nat
%   postulate
%     Sort   : Set
%     Clause : Set
%     Name : Set
%     Visibility : Set
%     Literal : Set
%     Meta : Set
%   data Arg {a} (A : Set a) : Set a where
%   data Abs {a} (A : Set a) : Set a where
%   data Term : Set
%   Type = Term
% \end{code}
%
% The actual innternal data representation is very compact:
% \begin{code}
%   data Term where
%     var       : (x : ℕ) (args : List (Arg Term)) → Term
%     con       : (c : Name) (args : List (Arg Term)) → Term
%     def       : (f : Name) (args : List (Arg Term)) → Term
%     lam       : (v : Visibility) (t : Abs Term) → Term
%     pat-lam   : (cs : List Clause) (as : List (Arg Term)) → Term
%     pi        : (a : Arg Type) (b : Abs Type) → Term
%     agda-sort : (s : Sort) → Term
%     lit       : (l : Literal) → Term
%     meta      : (x : Meta) → List (Arg Term) → Term
%     unknown   : Term
%
%   data Definition : Set where
%     function    : (cs : List Clause) → Definition
%     data-type   : (pars : ℕ) (cs : List Name) → Definition
%     record-type : (c : Name) (fs : List (Arg Name)) → Definition
%     data-cons   : (d : Name) → Definition
%     axiom       : Definition
%     prim-fun    : Definition
% \end{code}
