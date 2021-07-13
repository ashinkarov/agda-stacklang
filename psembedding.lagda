\begin{code}[hide]

module psembedding where

open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; s≤s; z≤n; _≤ᵇ_) renaming (_∸_ to _-_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit using (⊤; tt)

open import Function using (case_of_; flip)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import Relation.Nullary
open import Relation.Nullary.Decidable

-- Debug
open import ReflHelper
open import Agda.Builtin.Reflection
import Data.List as L

variable
  X Y Z : Set
  S : Set
  M : Set → Set
  @0 k l m n : ℕ

\end{code}

% PostScript Language and its embedding
\section{PostScript and its embedding in Agda} \label{sec:embedding}

PostScript is a document description language, and besides the usual markup,
it is possible to define arbitrary computations.  The language is dynamically typed
and stack-based.  That is, there is a notion of a global stack, which
is used for both, passing values and storing results.  All the commands
are argumentless operators, and a program is a chain of such commands.
For example, consider a function that computes $a^2 + b^2$, where $a$ and
$b$ are the top two stack values.
\begin{lstlisting}[language=PostScript]
dup   % a b b    duplicate top element
mul   % a b*b    multiply top two numbers
exch  % b*b a    excange top two elements
dup   % b*b a a  duplicate top element
mul   % b*b a*a  multiply top two numbers
add   % b*b+a*a  add top two numbers
\end{lstlisting}

Commands use mnemonic names and typically implement
a simple computation or element manipulation on the stack.  Recursive
function definitions are written as follows:

%  % n -- fib(n)
%  dup dup      % n n n
%  0 eq exch    % n n==0 n
%  1 eq         % n n==0 n==1
%  or           % n (n==0 || n==1)
%  { pop 1 }    % 1
%  {
%    dup        % n n
%    1 sub fib  % n fib(n-1)
%    exch       % fib(n-1) n
%    2 sub fib  % fib(n-1) fib(n-2)
%    add        % fib(n-1)+fib(n-2)
%  } ifelse
\begin{lstlisting}[language=PostScript]
/fib {
  dup 0 eq           % n n==0
  { pop 1 }          % 1
  { dup 1 eq         % n n==1
    { pop 1 }        % 1
    { dup 1 sub fib  % n fib(n-1)
      exch 2 sub fib % fib(n-1) fib(n-2)
      add            % fib(n-1)+fib(n-2)
    } ifelse
  } ifelse
} def
\end{lstlisting}

A function is defined with the slash name (`fib' in the above example),
followed by a block of commands that are written within braces (the
body of the function) followed by the \textbf{def} command.  Definitions may be
used as regular commands, including recursive calls.
In the body of the function, we check whether the argument
(the top stack element) is zero, in which case we remove it
from the stack and put the value one.  Otherwise, we duplicate the argument,
subtract one, make a recursive call, and multiply the result with the
original argument.  Conditional are expressed with two code blocks
followed by the \textbf{ifelse} command.

By drawing the results of the fib function (code not shown here), we
can obtain the following picture using a PostScript interpreter:

\epsfbox[0 0 200 100]{1.ps}

\subsection{Assumptions}

Before we proceed to the actual embedding, we would like to clarify our
assumptions about the chosen subset of PostScript and explain what
do we expect from the embedding.

We consider a very small subset of PostScript that is sufficient to express
functions on natural numbers.  While PostScript has many more commands,
types, and drawing primitives, for presentational purposes, we chose the
smallest subset that is sufficient to demonstrate verification problems.
This keeps our extractor complexity very low, and makes the examples
transferable to other stack-based languages such as Forth.

The main focus of our Agda embedding is to track the number of elements
on the stack.  On the one hand this helps to entirely avoid stack underflows
--- an extremely often practical problem in stack-based programs.  On the
other hand, by doing so, we almost immediately run into necessity to use
dependent types in the embedded programs.  The other points that we
want to demonstrate in the embedding are: i) attaching arbitrary properties
to function arguments (see \AF{index} and \AF{for} functions);
ii) guaranteeing function termination; and iii) using runtime-irrelevance
annotations to guarantee that extra properties do not have any computational
meaning.

\subsection{Embedding in Agda}

Our Agda embedding defines a stack type and a number of basic operators
operating on it.

\paragraph{Stack type}
We define the type of our stack inductively, and we force the type to carry
its length. Per our assumptions, the stack can only store elements of type
\AD{ℕ}.
\begin{code}
data Stack : @0 ℕ → Set where
  []   : Stack 0
  _#_  : Stack n → ℕ → Stack (suc n)
\end{code}
\begin{code}[hide]
infixl 5 _#_
variable s : Stack n
\end{code}
Similarly to vectors, the \AD{Stack} type has two constructors: \AC{[]} for stacks of length
zero and \AC{\_\#\_} for stacks of length $1 + n$.  For example,
a stack of three natural numbers can be built as follows:
\begin{code}
ex₁ : Stack 3
ex₁ = [] # 1 # 2 # 3
\end{code}
We defined \AC{\_\#\_} to be left-associative, therefore we do not put any parenthesis.

\paragraph{Basic Operations}

\begin{code}[hide]
tl : Stack (1 + n) → Stack n
tl (xs # _) = xs
\end{code}

The basic stack operations are defined as functions from \AD{Stack} to \AD{Stack}.
The type index makes it possible to capture precisely the effect of each
operation.  For example:
\begin{code}
push : ℕ → Stack n → Stack (1 + n)
push x xs = xs # x

pop : Stack (1 + n) → Stack n
pop (xs # x) = xs

dup : Stack (suc n) → Stack (2 + n)
dup (xs # x) = xs # x # x

exch : Stack (2 + n) → Stack (2 + n)
exch (xs # x # y) = xs # y # x

add mul : Stack (2 + n) → Stack (1 + n)
add (s # x # y) = s # x + y
mul (s # x # y) = s # x * y
\end{code}
\begin{code}[hide]
clear : Stack n → Stack 0
clear _ = []

sub eq gt : Stack (2 + n) → Stack (1 + n)
sub (s # x # y) = s # x - y
eq  (s # x # y) = s # (if x ℕ.≡ᵇ y then 1 else 0)
gt  (s # x # y) = s # (if x ℕ.≤ᵇ y then 0 else 1)
\end{code}

As it can be seen, the nature of these operations is straight-forward.  However,
note that the length index of \AD{Stack} ensures that the body of the function
respects the specification.  If the body of the function returns the stack that
does not have the length prescribed by the type, such a function would not typecheck.

\begin{comment}
Consider the \AD{count} function that computes the length of the stack and stores
it as the top element.  While it would be tempting to implement this function as
\begin{code}
--count : Stack ℕ n → Stack ℕ (1 + n)
--count s = s # n
\end{code}
Such a code would not typecheck, because \AB{n} is bound as a runtime-irrelevant argument.
We can use arbitrary expressions that depend on \AD{n} in irrelevant positions,
but not when constructing the result.  This irrelevance annotation gives us a clear
separation between the variables that we use for verification and that we use for
computations.  One way to implement \AD{count} is:
\begin{code}
count : Stack n → Stack (1 + n)
count xs = xs # go xs
  where
    go : Stack n → ℕ
    go []       = 0
    go (xs # _) = suc (go xs)
\end{code}
\end{comment}

%For simplicity we do not define subtraction and division, as when operating
%strictly in natural numbers, these functions would require additional proofs.
%We will need a proof that $a > b$ when subtracting $a - b$, and we will need
%a proof that $b \not= 0$ when dividing $a / b$.

%Finally, we define arithmetic operations using a helper function \AD{binop}
%that always acts on the two topmost elements of the stack.
%\begin{code}
%binop : (X → X → X) → Stack (2 + n) → Stack (1 + n)
%binop f (xs # x # y) = xs # f x y
%
%add sub mul eq gt : Stack ℕ (2 + n) → Stack ℕ (1 + n)
%add  = binop _+_
%sub  = binop _-_
%mul  = binop _*_
%eq   = binop (λ x y → if x ℕ.≡ᵇ y then 1 else 0)
%gt   = binop (λ x y → if x ℕ.≤ᵇ y then 0 else 1)
%\end{code}


We define several operations that do not represent PostScript
commands, but that will be useful in some of the examples.
The \AF{subst-stack} command makes it possible to cast a
stack of length $m$ into the stack of length $n$, given
a proof that $m \equiv n$.
\begin{code}
subst-stack : @0 m ≡ n → Stack m → Stack n
subst-stack refl xs = xs
\end{code}
In dependently typed langauges, $m$ and $n$ can be arbitrary
expressions, and it is not always obvious to Agda that these are
equal.  For example, if we require a stack of length $m + n$, but
we have a stack of length $n + m$, we cannot blindly use it, as
this would not typecheck.  However, we can solve the problem by
using \AF{subst-stack} and providing a proof that
$m + n \equiv n + m$.

We also define the PostScript command \AF{index} that
makes it possible to access any element of the stack by providing
its offset.  This can be seen as a more general version of the
\AF{dup} command.  We first implement a helper function \AF{get-index}
that does the actual indexing (we only give a signature), and then
\AF{index} puts the element obtained by \AF{get-index} on the stack.
Notice that both functions require a proof that the index is within
bounds.  Also, we are not strictly following the semantics of
PostScript, as the index must be passed explicitly, rather
than taking it from the stack.
\begin{code}
get-index : (k : ℕ) → @0 k < m → Stack m → ℕ
index : (k : ℕ) → @0 k < m → Stack m → Stack (1 + m)
index k k<m xs = xs # get-index k k<m xs
\end{code}
\begin{code}[hide]
get-index zero     (s≤s k<m) (xs # x) = x
get-index (suc k)  (s≤s k<m) (xs # x) = get-index k k<m xs
\end{code}

Finally, we implement a convenience function \AF{≤-ok} that
can automatically find simple proofs that some $x$ is less or
equal than some $y$.
\begin{code}
≤-ok : {x y : ℕ} → {w : True (x ≤? y)} → x ≤ y
≤-ok {w = w} = toWitness w
\end{code}
While this might look a bit like magic, the core idea is that
\AF{≤?} is a decision procedure, and \AF{True} forces normalisation
of \AB{x} \AF{≤?} \AB{y}.  In case normalisation is enough to compute the answer,
there is a standard way to turn \AB{w} into the proof of inequality.
Practically, we often get away with using \AF{≤-ok} in places where
a simple proof is needed.

We explicitly forego the definition of conditionals and comparison
operators in favour of using pattern-matching functions.  Recursion
is essential part of Agda, so there is no need to introduce any new
operators.  Later we will demonstrate how can we add a for-loop to
the embedding.

Note that nothing in this shallow embedding prevents us from doing
operations that are illegal in PostScript, such as duplicating the
whole stack or discarding it altogether. Such properties could be
enforced by using an (indexed) monad for stack operations, or by
working in a quantitative type theory such as Idris 2~\cite{TODO}.
Here we take a more straightforward approach by simply rejecting these
illegal programs in our extractor.

\subsection{Examples}

Let us consider a typical program in the proposed embedding.
Per our assumption, we express all the
operations in terms of base functions defined above.  We
start with a trivial function that adds one to the top element of
the stack.

\begin{code}
add-1 : Stack (1 + n) → Stack (1 + n)
add-1 s = add (push 1 s)
\end{code}

We are required to define the type, which in turn forces us to specify
how does the operation change the length of the stack.  Stack
operators are regular functions, so the chain of applications would be
written in reverse, when comparing to the corresponding PostScript
program.  While this does not affect functionality, it may be
aesthetically pleasing to maintain the original order of operators.
This can be achieved by defining an operation \AF{\_▹\_} that reverses
the arguments in application (this is Haskell's \$ operator):

\begin{code}[hide]
infixl 5 _▹_
\end{code}
\begin{code}
_▹_ : X → (X → Y) → Y
x ▹ f  = f x
\end{code}
\begin{code}[hide]
-- not sure if we need to expose this in the text
{-# INLINE _▹_ #-}
add-1′ : Stack (1 + n) → Stack (1 + n)
\end{code}
Now we can rewrite the above example as:
\begin{code}
add-1′ s = s ▹ push 1 ▹ add
\end{code}

% This function does nothing to the stack but it introduces
% a bunch of runtime irrelevant argumetns.
%
% \begin{code}
% stack-id : (s : Stack ℕ 1) → {@0 b : m ℕ.> 0} → Stack ℕ 1
% stack-id xs@(t # h) = (t # h)
% \end{code}
%
% These two functions demonstrate a trivial case when one function
% calls another function.
%
% \begin{code}
% add1 : Stack ℕ (1 + n) → Stack ℕ (1 + n)
% add1 xs = add (push 1 xs)
%
% dblsuc : Stack ℕ (1 + n) → Stack ℕ (2 + n)
% dblsuc xs = add1 (dup xs)
% \end{code}


Consider now a slightly more complicated function that computes
$a^2 + b^2$ where $a$ and $b$ are top two elements of the stack:
\begin{code}
sqsum : Stack (2 + n) → Stack (1 + n)
sqsum s = s ▹ dup ▹ mul ▹ exch ▹ dup ▹ mul ▹ exch ▹ add
\end{code}
It can be easier to understand the code if we introduce internal
stack states in variables names of let:
\begin{code}
sqsum′ : Stack (2 + n) → Stack (1 + n)
sqsum′ s:a:b = let s:a:b*b    = s:a:b      ▹ dup   ▹ mul
                   s:b*b:a*a  = s:a:b*b    ▹ exch  ▹ dup ▹ mul
                   s:a*a:b*b  = s:b*b:a*a  ▹ exch
               in  s:a*a:b*b ▹ add
\end{code}
Notice that in Agda, variable/function names are chains of almost
arbitrary symbols with no spaces.

\paragraph{Pattern Matching}
The only way to express conditional in the proposed embedding is
by means of pattern matching.  Consider the implementation of the
fibonacci example:

\begin{code}[hide]
module FibNonTerm where
\end{code}
\begin{code}
  {-# TERMINATING #-}
  fib : Stack (1 + n) → Stack (1 + n)
  fib s@(_ # 0)             = s ▹ pop   ▹ push 1
  fib s@(_ # 1)             = s ▹ pop   ▹ push 1
  fib s@(_ # suc (suc x))   = s ▹ dup   ▹ push 1 ▹ sub ▹ fib
                                ▹ exch  ▹ push 2 ▹ sub ▹ fib
                                ▹ add
\end{code}
The only unusual thing here is that we match the structure of the stack
and the structure of the element simultaneously.
For now, it is an excercise to the reader to verify that \AF{fib}
actually implements fibonacci numbers.  In a later section we will give
a formal proof of that.

Note that Agda does not see that the \AF{fib} function terminates.
For now, we add an explicit annotation, but in a later
ection we will demonstrate how to deal with this formally.



\paragraph{Dependent Stack Length}
So far all the specifications within the embedded language did not
require dependent types, and could be encoded in languages with a weaker
type system such as Haskell or OCaml.  However, it becomes very clear
that even simplest programs in stack languages may expose a dependency
between the stack argument and the stack length.  Those cases cannot
be expressed in non-dependently-typed host languages.  A simple example
of such a program is a function \AF{rep} that replicates the $x$ value $n$ times,
where $x$ and $n$ are top two stack elements.
Here is a possible implementation of that function:

\begin{code}
hd : Stack (1 + n) → ℕ
hd (_ # x) = x
\end{code}
\begin{code}[hide]
module RepSimple where
    open import Data.Nat using (s≤s; z≤n)
\end{code}
\begin{code}
    {-# TERMINATING #-}
    rep : (s : Stack (2 + n)) → Stack (hd s + n)
    rep       s@(_ # _ # zero)   = s ▹ pop ▹ pop
    rep s:x:m+1@(_ # _ # suc m)  =
         let s:x:m    = s:x:m+1  ▹ push 1 ▹ sub
             s:x:m:x  = s:x:m    ▹ index 1 ≤-ok
             s:x:x:m  = s:x:m:x  ▹ exch
         in  subst-stack (+-suc _ _) (rep s:x:x:m)
\end{code}

First, we define the \AD{hd} helper function that returns the top element
of the stack.  We use this function to specify the length of the stack
returned by \AD{rep}.  This length is the value of the top element of the
stack when entering the function the first time.  In case this argument
is zero, we remove two elements from the stack: the argument we were
replicating, and the count argument.  Otherwise, we decrease the count,
copy the argument we are replicating, and put them in the expected position
to make the next recursive call.  The second argument to \AF{index} is a
proof that $1 < 2 + n$, which Agda can compute automatically using \AF{≤-ok}.
At the end we apply
\AF{subst-stack} to fit the type definition.  The length of \AF{rep} \AB{s:x:x:m}
is $(m + (1 + n))$ whereas we need the length
$(1 + (m + n))$.  Such an equality is not obvious to Agda, we
apply the \AD{+-suc} function from the standard library that translates
between these expressions.

\paragraph{Extrinsic Verification}
The nature of dependently-typed systems makes it possible not only to
specify functions with intrinsic constraints, such as length of the stack,
but also to prove some properties about existing functions as theorems.  For
example, we can prove that \AF{sqsum} actually implements the sum of squares:
\begin{code}
sqsum-thm : sqsum (s # k # l) ≡ s # k * k + l * l
sqsum-thm = refl
\end{code}
The theorem says that for any $s$, $k$ and $l$, application of \AD{sqsum} to
$s$ appended with $k$ and $l$ equals to $s$ appended with $k^2 + l^2$.  Luckily,
from the way we constructed the basic operations, this fact is obvious to Agda.
So the proof is simply the \AC{refl}exivity constructor.

On the other hand, proving that \AF{fib} matches a simpler specification that
we call \AF{fib-spec} requires a bit more work.
\begin{code}[hide]
module FibNonTermPf where
  open FibNonTerm
\end{code}
\begin{code}
  fib-spec : ℕ → ℕ
  fib-spec 0 = 1
  fib-spec 1 = 1
  fib-spec (suc (suc x)) = fib-spec (suc x) + fib-spec x
\end{code}
This is an inductive proof where we consider two base cases, and the
step case.  In the latter we refer to the theorem with a structurally
smaller arguments, and after rewriting such cases, the statement becomes
obvious.
\begin{code}
  fib-thm : (s : Stack n) (x : ℕ) → fib (s # x) ≡ s # fib-spec x
  fib-thm _ 0 = refl
  fib-thm _ 1 = refl
  fib-thm s (suc (suc x))
    rewrite  (fib-thm (s # suc (suc x)) (suc x))
          |  (fib-thm (s # fib-spec (suc x)) x)  = refl
\end{code}


\paragraph{Proving Termination}
At this point, we have seen how to write programs in the embedding, express
non-trivial properties related to the length of the stack, and verify that
a function evaluates to the same results as some other function.  One remaining
problem is that for some functions, Agda cannot automatically prove termination.
However, as long as a programmer is happy to take responsibility by putting
the annotation, we can immediately proceed to extraction.

We demonstrate a way to prove termination of the functions from previous
sections.
%
The problem with \AF{rep} is that the recursive call happens on the stack
that is became one element bigger, yet the top element decreased by one.
Therefore, this argument is not strictly smaller, and there are no other
decreasing arguments, so the termination checker fails to accept this
definition.  A standard way to fix this is to add an extra argument to
the function, and define a relation that depends on that argument in a
such a way that the argument decreases.  In \AF{rep} case we add the
new argument \AB{k}, and we define a relation that the top of the stack
is definitionally equal to \AB{k}:

\begin{code}[hide]
module RepTerm where
    open import Data.Nat using (s≤s; z≤n)
\end{code}
\begin{code}
    rep′ : (s : Stack (2 + n)) → @0{hd s ≡ k} → Stack (hd s + n)
    rep′ {k = 0}      s@(_ # _ # zero)         {refl}  = s ▹ pop ▹ pop
    rep′ {k = suc m}  s:x:m+1@(_ # _ # suc m)  {refl}  =
         let s:x:m    = s:x:m+1  ▹ push 1 ▹ sub
             s:x:m:x  = s:x:m    ▹ index 1 ≤-ok
             s:x:x:m  = s:x:m:x  ▹ exch
         in  subst-stack (+-suc _ _) (rep′ {k = m} s:x:x:m {refl})

    rep : (s : Stack (2 + n)) → Stack (hd s + n)
    rep s = rep′ s {refl}
\end{code}
As the function is pattern-matching on the top of the stack, and the
only value of the \AD{\_≡\_} type is \AC{refl}, the argument \AB{k}
has to be \AN{0} in the first case, and \AC{suc} \AB{m} in the second
case.  This ensures that \AF{rep′} is structurally decreasing in \AB{k},
and the function is accepted by the termination checker.


% New implicit variables fucked-up the code in FibTerm
%
%
% \begin{code}
% _++_ : ∀ {X m n} → Stack X m → Stack X n → Stack X (n + m)
% xs ++ [] = xs
% xs ++ (ys # y) = xs ++ ys # y
%
% split : ∀ {X}{n} → (m : ℕ) → Stack X (m + n) → Stack X n × Stack X m
% split zero xs = xs , []
% split (suc m) (xs # x) =
%   let ys , zs = split m xs
%   in  ys , zs # x
%
% iframep : ∀ {X m n k} {P : Stack X m → Set}
%         → ((s : Stack X m) → @0 (P s) → Stack X n)
%         → (xs : Stack X (m + k))
%         → @0 (P (proj₂ (split m xs)))
%         → Stack X (n + k)
% iframep {m = m} f xs p =
%   let (ys , zs) = split m xs
%   in ys ++ (f zs p)
%
%
% module FibTerm where
%   open import Data.Nat using (_<_; s≤s; z≤n)
%   open import Function using (_$_)
%
%   fib′ : ∀ {@0 y} → (s : Stack ℕ (1 + n)) → @0 {hd s < y} → Stack ℕ (1 + n)
%   fib′ s@(_ # 0) = s ▹ pop ▹ push 1
%   fib′ s@(_ # 1) = s ▹ pop ▹ push 1
%   fib′ {n = n}{y = .suc y} xs@(l # r@(suc (suc x))) { s≤s x<y } =
%     let
%       l:r:r-1        = sub $ push 1 $ dup xs
%       l:r:fib[r-1]   = iframep {m = 1} {P = λ s → suc x ≡ hd s}
%                               (λ s hd[s]≡suc[x] → fib′ s { subst (_< y) hd[s]≡suc[x] x<y })
%                               l:r:r-1 refl
%       l:fib[r-1]:r-2 = sub $ push 2 $ exch l:r:fib[r-1]
%     in                 add $ fib′ l:fib[r-1]:r-2
%                                   { fib-thm {ys =  fib′ ([] # suc x)} (<-trans ≤-refl x<y) }
%    where
%     fib-thm : ∀ {n}{xs : Stack ℕ n}{ys : Stack ℕ 1}{x}{l}
%             → x < l → hd (sub (exch ((xs # suc (suc x)) ++ ys) # 2)) < l
%     fib-thm {ys = [] # y} x<l = x<l
%
%   fib : ∀ {n} → Stack ℕ (1 + n) → Stack ℕ (1 + n)
%   fib xs = fib′ xs {≤-refl}
% \end{code}


Showing termination of the \AF{fib} function fails for the same reason
as in case of \AF{rep} --- it is unclear whether any argument decreases when
calling \AF{fib} recursively.  Unfortunately, we cannot use the above trick
with relation as is, because we make two recursive calls, but we keep results
on the same stack.  The problem is that after the first recursive call \AF{fib}
\AB{s:x:x-1} we obtain (conceptually) a new stack.  In order to call \AF{fib}
on $x - 2$ we first apply \AF{exch} to the result of the first recursive call
(to bring \AB{x} at the top).  However, we cannot prove that \AF{fib} only
modified the top element of the stack and did not touch other elements.

\begin{comment}
There is a number of ways we can fix this, but for presentatoinal purposes
we show the shortest one.  We adjust the structure of our recursion,
so that we deal with three elements per iteration, implementing a simple
scheme $\langle 1+x, a, b \rangle \leadsto \langle x, b, a+b \rangle$.
Where $x$ is the number in the sequence that we want to find, and $a = b = 1$
in the initial call:

\begin{code}
rot3 : Stack (3 + n) → Stack (3 + n)
rot3 (s # a # b # c) =  s # c # b # a
\end{code}
\begin{code}[hide]
module Fib3 where
    open import Data.Nat using (_<_; s≤s; z≤n)
    open import Function using (_$_)
\end{code}
\begin{code}
    fib3 : (s : Stack (3 + n))
         → @0{get-index 2 ≤-ok s ≡ k}
         → Stack (3 + n)
    fib3 {k = .0}     s@(_ # 0        # a # b) {refl} = s
    fib3 {k = .suc k} s@(_ # (suc m)  # a # b) {refl} =
      let s:1+m:a:b    = s
          s:1+m:b:a+b  = s:1+m:a:b   ▹ exch ▹ index 1 ≤-ok ▹ add
          s:a+b:b:m    = s:1+m:b:a+b ▹ rot3 ▹ push 1 ▹ sub
          s:m:b:a+b    = s:a+b:b:m   ▹ rot3
      in  fib3 {k = k} s:m:b:a+b {refl}

    fib : Stack (1 + n) → Stack (1 + n)
    fib s =
      let s:m:1:1              = s ▹ push 1 ▹ push 1
          s:0:fib[m]:fib[1+m]  = fib3 s:m:1:1 {refl}
      in  s:0:fib[m]:fib[1+m] ▹ pop ▹ exch ▹ pop
\end{code}
Then \AF{fib3} is doing the iteration; \AF{fib} sets the inital seed
and cleans-up the stack.  We defined a new stack operation
called \AF{rot3} that reverses the top three elements of the stack.
Note that this is not a built-in operation of PostScript, but it is
trvial to implement it in terms of \AF{roll} and \AF{exch}.
\end{comment}

\subsection{For Loop}
The final part of our embedding is the for-loop construct.  Not only
this is often found in practical PostScript documents, it also helps
to avoid the problem with proving termination.  The difficulty with
encoding the for-loop behaviour lies in its potential ability to
arbitrarily modify stack at every iteration.  While there is no
technical problem to encode such a behaviour in Agda, it would be
quite inconvenient to work with.  Every time one needs to ensure
that a stack returned by a for-loop contains enough elements, a
potentially complex proof has to be given.  We can make our life
easier by working with a simpler version of the for loop that assumes
the same stack size at each iteration, which is sufficient for our
examples. Concretely, the boundaries
of the loop are given by two numbers $s$ and $e$, where
the loop iterates through indices $s, 1+s, \dots, e$.

We define for-loop as a function of two arguments: the body
of the for-loop given by a function and the initial stack.
\begin{code}
for : (Stack (1 + n) → Stack n) → Stack (2 + n) → Stack n
for {n} f (st # s # e) = if s ≤ᵇ e then loop (e - s) st else st
  where
  loop : ℕ → Stack n → Stack n
  loop zero     st = st ▹ push s ▹ f
  loop (suc i)  st = st ▹ loop i ▹ push (suc i + s) ▹ f
\end{code}
The initial stack contains 2 loop boundary elements and $n$ other
elements. It computes the number of iterations \AB{i} and unrolls the
loop that many times, each time pushing the current value of the loop
variable to the top of the stack. In the end, it finishes with a stack
with \AB{n} elements. If the lower boundary is already above the upper
boundary initially, it removes both of them and returns immediately.

\begin{code}[hide]
-- 10 + 0 + 1 + ... + x
sum-for : Stack (1 + n) → Stack (1 + n)
sum-for s@(_ # x) = s ▹ push 10 ▹ exch ▹ push 0 ▹ exch
                      ▹ for add
\end{code}

Now we are ready to define our running fibonacci example using \AF{for}:
\begin{code}
fib-for : Stack (1 + n) → Stack (1 + n)
fib-for s@(_ # x)
    = (s ▹ push 0 ▹ exch ▹ push 1 ▹ exch ▹ push 0 ▹ exch)
    ▹ for (λ s → s ▹ pop ▹ exch ▹ index 1 ≤-ok ▹ add)
    ▹ pop
\end{code}
Our initial stack contains the function argument $x$ at the top. We modify
the stack by inserting $0$ and $1$ (inital fibonacci seeds) and $0$ (the lower bound for the for loop) before $x$.  In the function body, we remove the iteration value,
and modify $\langle a , b\rangle$ into $\langle b , a+b\rangle$.
%Note that we start from 0 1 and not 1 1, as the loop goes from 0 to $x$
%inclusively.  Alternatively, we could have conditionalise on $x$.
\begin{code}[hide]
module Sierpinski where
\end{code}

We now consider a more realistic PostScript example that generates an
image of Sierpinski fractal.  The structure of the code is
straightforward: it consists of a doubly-nested for loop, which draws
a dot at each coordinate $(i,j)$ where the bit-wise `and' of $i$ and
$j$ is not zero.
%
For this example we assume that a drawing function and bit-wise `and'
are already defined in PostScript, so we postulate them in Agda.  This
means that we only provide a type signature of the functions, but not
the implementaiton.
%
We implement conditional drawing via the helper function \AF{draw-if}.
\begin{code}
    postulate
      draw-circ-xy : Stack (2 + n) → Stack n
      bit-and : Stack (2 + n) → Stack (1 + n)

    draw-if : Stack (3 + n) → Stack (2 + n)
    draw-if s@(_ # 0)  = s  ▹ pop ▹ index 1 ≤-ok ▹ index 1 ≤-ok
                            ▹ draw-circ-xy
    draw-if s          = s  ▹ pop
\end{code}
The main function sets the boundaries for both for-loops, applies
\AF{bit-and} to $i$ and $j$, and calls the drawing function, ensuring
that no extra arguments are left on the stack.
\begin{code}
    sierp : Stack (1 + n) → Stack n
    sierp s  =
      s ▹ push 0 ▹ index 1 ≤-ok
        ▹ for (λ s → s ▹ push 0 ▹ index 2 ≤-ok
                       ▹ for (λ s → s ▹ index 1 ≤-ok
                                      ▹ index 1 ≤-ok
                                      ▹ bit-and ▹ draw-if ▹ pop)
                       ▹ pop)
        ▹ pop
\end{code}
While the algorithm is straightforward, it is very easy to forget to
remove or copy an element within for-loops when implementing such
a code manually.  Strict stack size discipline that we have in Agda
comes very helpful here, and eliminates an entire class of errors.
