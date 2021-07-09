\begin{code}[hide]

{-# OPTIONS --rewriting #-}

module reduction where

open import Agda.Builtin.Equality.Rewrite

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_) renaming (_∸_ to _-_)
open import Data.Nat.Properties
open import Data.List
open import Data.Product
open import Data.String as S using (String; _≈?_; lines)
open import Data.Unit

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import Reflection as R using (TC; Name; Names; Term)
import      Reflection.TypeChecking.Monad.Syntax as R

open import psembedding
open import extraction
\end{code}


\section{Partial evaluation} \label{sec:partial-evaluation}

Working with a shallow embedding brings us gives us an important
benefit: we can use the existing evaluator of Agda to partially
evaluate programs prior to extraction. In this section, we give a
couple of examples of how this can be useful. We also demonstrate how
to extend Agda's evaluator with domain-specific optimizations through
the use of \emph{rewrite rules}.

\paragraph{Using Agda functions as macros}

\todo[inline]{We could also mention that we are relying on \AF{\_▹\_}
and friends to be inlined, so that we don't have to specialcase them
in the extractor.}
By reducing Agda expressions prior to extraction, we may use any host
language constructs that are not present in the embedding, as long as
they can be eliminated prior to extraction. For example, we can make
use of the Agda function \AF{applyN} to apply a certain postscript
operator \AB{n} times:

\begin{code}
applyN : ℕ → (X → X) → X → X
applyN zero     f x = x
applyN (suc n)  f x = f (applyN n f x)

pow32 : Stack ℕ (1 + n) → Stack ℕ (1 + n)
pow32 s = applyN 5 (λ s → s ▹ dup ▹ mul) s
\end{code}

The function \AF{applyN} is a polymorphic and higher-order function,
so it falls well outside the fragment of Agda that our extractor can
deal with. Nevertheless, we can ask the extractor to inline the
definition of \AF{applyN}, which then makes it possible to extract the
definition of \AF{pow64}:

\begin{code}
_ : lines (extract pow32 base base) ≡
  ( "/pow32 {"
  ∷ "  dup mul dup mul dup mul dup mul dup mul"
  ∷ "} def"
  ∷ [] )
_ = refl
\end{code}

In essence, this allows us to write macros using arbitrary Agda
functions, as long as the end result falls within the fragment that
the extractor knows how to deal with.

\paragraph{Partial evaluation of primitive operators}

In addition to inlining external functions, the extractor can also
simplify expressions that involve basic operations such as \AF{push}
and \AF{pop}. To achieve this, we simply pass an empty list as the
third argument to the \AF{extract} macro (which is the list of
functions that should not be inlined). For example, it can eliminate
values that are first pushed and then popped again without being used:

\begin{code}
push-pop : Stack ℕ n → Stack ℕ n
push-pop s = s ▹ push 42 ▹ pop

_ : lines (extract push-pop base []) ≡
  ( "/push-pop {"
  ∷ "  "
  ∷ "} def"
  ∷ [] )
_ = refl
\end{code}






\paragraph{Domain-specific optimizations as rewrite rules}

A common way to define domain-specific compiler optimizations is through
the specification of \emph{rewrite rules} that rewrite terms matching
a given pattern to an equivalent form that is either more efficient
or reveals further optimization opportunities.
%
By giving a shallow embedding of our target language in Agda, we have
the opportunity to define \emph{verified} rewrite rules, providing
a proof that the left- and right-hand side of the rewrite rule are
equivalent.
%
To achieve this, we could define our own representation of verified
rewrite rules and integrate them into the extractor.
%
However, we can avoid the effort of doing so since Agda already has a
built-in concept of rewrite rules.

Rewrite rules were originally introduced to Agda to work around the
limitations of definitional equality in intentional type theory.
%
For example, it can be used to make $0 + x$ definitionally equal to
$x + 0$.
%
Since we work with a shallow embedding, these rewrite rules are
equally well suited to optimize the embedded programs we write before
they are extracted.

As an example, we can prove that first pushing \AN{0} to the stack and
then calling \AF{add} does not have any effect.

\begin{code}
add-0-cancel : (s : Stack ℕ (1 + n)) → s ▹ push 0 ▹ add ≡ s
add-0-cancel (s # x) = cong (s #_) (+-identityʳ x)
\end{code}

Next, we can register this equality as a rule to be applied
automatically during evaluation by using a \AK{REWRITE} pragma:

\begin{code}
{-# REWRITE add-0-cancel #-}
\end{code}

From now on the rule will be applied automatically by the extractor
whenever it can:

\begin{code}
add-some-numbers : Stack ℕ (1 + n) → Stack ℕ (1 + n)
add-some-numbers s = s  ▹ push 0 ▹ add  ▹ push 2 ▹ add
                        ▹ push 7 ▹ add  ▹ push 0 ▹ add

_ : lines (extract add-some-numbers base []) ≡
  ( "/add-some-numbers {"
  ∷ "  2 add 7 add"
  ∷ "} def"
  ∷ [] )
_ = refl
\end{code}

We can further optimize the example by adding another rule
that joins together two adjacent additions:

\begin{code}
add-add-join : (s : Stack ℕ (1 + n)) (k l : ℕ)
  → s ▹ push k ▹ add ▹ push l ▹ add ≡ s ▹ push (k + l) ▹ add
add-add-join (s # x) k l = cong (s #_) (+-assoc x k l)
{-# REWRITE add-add-join #-}

_ : lines (extract add-some-numbers base []) ≡
  ( "/add-some-numbers {"
  ∷ "  9 add"
  ∷ "} def"
  ∷ [] )
_ = refl
\end{code}

\begin{code}[hide]
-- Another example, pretty similar to the previous one.
add-sub-cancel : (s : Stack ℕ (1 + n)) (k : ℕ) → s ▹ push k ▹ add ▹ push k ▹ sub ≡ s
add-sub-cancel (s # x) k = cong (s #_) (m+n∸n≡m x k)

{-# REWRITE add-sub-cancel #-}

foo : Stack ℕ (1 + n) → Stack ℕ (1 + n)
foo s = s ▹ push 5 ▹ add ▹ push 5 ▹ sub

_ : lines (extract foo base []) ≡ "/foo {" ∷ "  " ∷ "} def" ∷ []
_ = refl

-- s ▹ push 0 ▹ add ≡ s

-- add (s # 5) # 5

\end{code}

\paragraph{Implementation details}

Partial evaluation of Agda terms is achieved by normalising \ie{}~by
applying reduction rules to (sub)terms until they turn into values or
neutral terms.
%
Agda's reflection API offers a function \AF{normalise} for this
purpose. However, using this function directly runs into two problems:

\begin{itemize}

\item The \AF{normalise} function only works on terms and not on
entire function definitions. Hence we need to manually traverse the
function definition and call \AF{normalise} on the body of each
individual clause. During the implementation of this traversal, we
were faced with the challenge of reconstructing the right typing
context for each clause.  Agda constructs this context internally
during elaboration of the clauses, but the reflection API did not
provide access to it. To solve this problem we
extended the reflection API to provide it for us (see
\url{https://github.com/agda/agda/pull/4722}).

\item The functionality to selectively normalise certain functions
while leaving others intact was not previously available in Agda. We
added two new primitives to the reflection API: \AF{dontReduceDefs}
and \AF{onlyReduceDefs}. (see
\url{https://github.com/agda/agda/pull/4978}).

\end{itemize}

These two changes to Agda were motivated by our goal to implement
custom extractors through reflection, but they are generally useful
for users of the reflection API. Both changes have been released as
part of Agda 2.6.2.
