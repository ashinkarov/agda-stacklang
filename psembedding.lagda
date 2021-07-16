\begin{code}[hide]

module psembedding where

open import Data.Bool using (Bool; true; false; if_then_else_; not; T)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_) renaming (_∸_ to _-_; _≤ᵇ_ to _≤_; _<ᵇ_ to _<_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit using (⊤; tt)

open import Function using (case_of_; flip)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

-- Debug
open import ReflHelper
open import Agda.Builtin.Reflection
import Data.List as L

variable
  X Y Z : Set
  @0 k l m n : ℕ
\end{code}

% PostScript Language and its embedding
\section{PostScript and its embedding in Agda} \label{sec:embedding}

PostScript is a document description language, and besides the usual markup,
it is possible to define arbitrary computations in it.  The language is dynamically typed
and stack-based.  That is, there is a notion of a global stack that
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
from the stack and put the value one.  The same for the case when the argument
is one.

\begin{wrapfigure}{r}{.33\columnwidth}
\epsfbox[17 10 80 65]{1.ps}
\caption{\label{fig:fib}Draw \AF{fib}.}
\end{wrapfigure}
Otherwise, we duplicate the argument, subtract one, make a recursive call.
Then we exchange the original argument with the result of the recursive call
by running \textbf{exch}.  We subtract two, make a recursive call and add results
of two recursive calls.   Conditionals are expressed with two code blocks
followed by the \textbf{ifelse} command.
In~\figref{fib} we draw the results of the fib function (code not shown here) using
a PostScript interpreter.

\paragraph{Assumptions}

We consider a small subset of PostScript that is sufficient to express
functions on natural numbers.  While PostScript has many more commands,
types, and drawing primitives, this subset is sufficient to demonstrate
the main challenges with verification and extraction.
This keeps the complexity of our extractor low, and makes the examples
transferable to other stack languages such as Forth.

The main focus of our Agda embedding is to track the number of elements
on the stack.  On the one hand this helps to entirely avoid stack underflows
--- an extremely frequent practical problem in stack-based programs.  On the
other hand, by doing so, we almost immediately run into necessity to use
dependent types in the embedded programs.  The other points that we
want to demonstrate in the embedding are: i) attaching arbitrary properties
to function arguments (see for example the \AF{index} function);
ii) guaranteeing function termination; and iii) using runtime-irrelevance
annotations to guarantee that extra properties do not have any computational
meaning.

\subsection{Embedding in Agda}

Our PostScript embedding in Agda consists of a type for stacks and a number
of basic functions operating on it.

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
\AC{[]} \AC{\#} \AN{1} \AC{\#} \AN{2} \AC{\#} \AN{3} is a stack of type \AD{Stack} \AN{3}.
We define \AC{\_\#\_} to be left-associative, therefore we do not need any parenthesis.
We annotate the index of \AD{Stack} as computationally irrelevant.
%by putting `@0' annotation in
%the definition of the type.

\paragraph{Basic Operations}

\begin{code}[hide]
tl : Stack (1 + n) → Stack n
tl (xs # _) = xs
\end{code}

The basic stack operations are defined as functions from \AD{Stack} to \AD{Stack}.
The type index makes it possible to capture precisely the effect of each
operation.
\begin{code}[hide]
push : ℕ → Stack n → Stack (1 + n)
pop : Stack (1 + n) → Stack n
dup : Stack (1 + n) → Stack (2 + n)
add mul : Stack (2 + n) → Stack (1 + n)
exch : Stack (2 + n) → Stack (2 + n)
\end{code}
\begin{code}
push  x s          = s # x        --: ℕ → Stack n → Stack (1 + n)
pop   (s # x)      = s            --: Stack (1 + n) → Stack n
dup   (s # x)      = s # x # x    --: Stack (1 + n) → Stack (2 + n)
exch  (s # x # y)  = s # y # x    --: Stack (2 + n) → Stack (2 + n)
add   (s # x # y)  = s # x + y    --: Stack (2 + n) → Stack (1 + n)
mul   (s # x # y)  = s # x * y    --: Stack (2 + n) → Stack (1 + n)
\end{code}
\begin{code}[hide]
clear : Stack n → Stack 0
clear _ = []

sub eq gt : Stack (2 + n) → Stack (1 + n)
sub (s # x # y) = s # x - y
eq  (s # x # y) = s # (if x ℕ.≡ᵇ y then 1 else 0)
gt  (s # x # y) = s # (if x ℕ.≤ᵇ y then 0 else 1)
\end{code}

In the types of these operations, the length index of \AD{Stack}
ensures that the body of the function respects the specification.  If
the body of the function returns the stack that does not have the
length prescribed by the type, such a function would not typecheck.

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
count s = s # go s
  where
    go : Stack n → ℕ
    go []       = 0
    go (s # _) = suc (go s)
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

Since the size of the stack is an expression that can contain free
variables as well as concrete numbers, it is not always possible for
Agda to see automatically that two stack sizes are equal. For example,
if we require a stack of length $m + n$, but we have a stack of length
$n + m$, we cannot blindly use it, as this would not typecheck.  To
deal with situations like this, we provide an operation
\AF{subst-stack} that cast a stack of length $m$ into the stack of
length $n$, given a (run-time irrelevant) proof that $m \equiv n$.
\begin{code}
subst-stack : @0 m ≡ n → Stack m → Stack n
subst-stack refl s = s
\end{code}
This operation does not have any run-time behaviour and will be
erased by the extractor.

We also define the PostScript command \AF{index} that
makes it possible to access any element of the stack by providing
its offset.  This can be seen as a more general version of the
\AF{dup} command.
%
The function \AF{index} requires a proof that the index is within
bounds.  Also, we are not strictly following the semantics of
PostScript, as the index is passed explicitly, rather
than taking it from the stack.
\begin{code}[hide]
infix 5 _!_
\end{code}
\begin{code}
_!_ : Stack m → (k : ℕ) → @0{T (k < m)} → ℕ
_!_ (s # x) zero            = x
_!_ (s # x) (suc k) {sk<m}  = (s ! k) {sk<m}

index : (k : ℕ) → @0{T (k < m)} → Stack m → Stack (1 + m)
index k {k<m} s = s # (s ! k) {k<m}
\end{code}
The proof that \AB{k} is less than \AB{m} is marked as implicit,
which means that Agda will automatically fill in the proof
(at least in the simple cases that we have in this paper).

We explicitly forego the definition of conditionals and comparison
operators in favour of using pattern-matching functions.  Recursion
is essential part of Agda, so there is no need to introduce any new
operators.  In \secref{for-loop} we demonstrate how to add a for-loop to
the embedding.

Nothing in this shallow embedding prevents us yet from doing
operations that are impossible to express in PostScript, such as duplicating the
whole stack or discarding it altogether. Such properties could be
enforced by using an (indexed) monad for stack operations, or by
working in a quantitative type theory such as Idris 2~\cite{Brady21-1}.
In this paper we take a more straightforward approach by rejecting these
illegal programs in our extractor.

\subsection{Examples}

Let us consider a typical program in the proposed embedding.
We express all the
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
For this purpose we define an operation \AF{\_▹\_} that reverses
the arguments in applications.  So we can rewrite the above example as:
%
\begin{code}[hide]
infixl 5 _▹_
add-1′ : Stack (1 + n) → Stack (1 + n)
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
_▹_ : X → (X → Y) → Y
x ▹ f  = f x
\end{code}}
\and
\codeblock{\begin{code}
add-1′ s = s ▹ push 1 ▹ add
\end{code}}
\end{mathpar}
\begin{code}[hide]
{-# INLINE _▹_ #-}
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


Consider now the example from \figref{sqsum} that computes
$a^2 + b^2$ where $a$ and $b$ are top two elements of the stack.
It can be easier to understand the code if we introduce names
for the intermediate states of the stack using \AK{let}:
\begin{code}
sqsum : Stack (2 + n) → Stack (1 + n)
sqsum s#a#b = let s#a#b*b    = s#a#b      ▹ dup   ▹ mul
                  s#b*b#a*a  = s#a#b*b    ▹ exch  ▹ dup ▹ mul
                  s#a*a#b*b  = s#b*b#a*a  ▹ exch
              in  s#a*a#b*b ▹ add
\end{code}
Agda identifiers are chains of almost arbitrary symbols with no
spaces, so \AB{s\#a*a\#b*b} is a valid variable name.

\paragraph{Pattern Matching}
The only way to express conditional in the proposed embedding is
by means of pattern matching.  Consider the implementation of the
fibonacci function:

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
actually implements fibonacci numbers. Below, we give a formal proof
\AF{✔} of this fact.

Note that Agda does not see that the \AF{fib} function terminates.
For now, we add an explicit annotation, but we demonstrate how to deal
with this in \secref{for-loop}.



\paragraph{Dependent Stack Length}
So far, all the specifications in the embedded language did not
require dependent types, and could be encoded in languages with a weaker
type system such as Haskell or OCaml.  However, it quickly becomes clear
that even simple programs in stack languages may expose a dependency
between the input stack and the size of the output stack.  Those cases
require dependent types to express statically.  An example
of such a program is a function \AF{rep} that replicates the $x$ value $n$ times,
where $x$ and $n$ are top two stack elements.
Here is a possible implementation of that function:

\begin{code}[hide]
module RepSimple where
    open import Data.Nat using (s≤s; z≤n)
\end{code}
\begin{code}
    {-# TERMINATING #-}
    rep : (s : Stack (2 + n)) → Stack ((s ! 0) + n)
    rep       s@(_ # _ # zero)   = s ▹ pop ▹ pop
    rep s#x#m+1@(_ # _ # suc m)  =
         let s#x#m    = s#x#m+1  ▹ push 1 ▹ sub
             s#x#m#x  = s#x#m    ▹ index 1
             s#x#x#m  = s#x#m#x  ▹ exch
         in  subst-stack (+-suc _ _) (rep s#x#x#m)
\end{code}


The length of the stack returned by \AD{rep} is given by the topmost
element of the input stack \AB{s} plus \AB{n}. Hence the size of the
output stack depends on the value of the input stack.
%
In case this argument
is zero, we remove two elements from the stack: the argument we were
replicating, and the count argument.  Otherwise, we decrease the count,
copy the argument we are replicating, and put them in the expected position
to make the next recursive call.
%
This results in the stack \AF{rep} \AB{s\#x\#x\#m} of size $(m + (1 +
n))$ while the expected size is $(1 + (m + n))$. It is not obvious to
Agda that these two sized are equal, so we apply
\AF{subst-stack} with the proof \AD{+-suc} from the standard library
to convert between these two sizes.

\paragraph{Extrinsic Verification}
The nature of dependently-typed systems makes it possible not only to
specify functions with intrinsic constraints, such as length of the stack,
but also to prove some properties about existing functions as theorems.  For
example, we prove that \AF{sqsum} actually implements the sum of squares:
\begin{code}
sqsum-thm : sqsum (s # k # l) ≡ s # k * k + l * l
sqsum-thm = refl
\end{code}
The theorem says that for any $s$, $k$ and $l$, application of \AD{sqsum} to
$s$ appended with $k$ and $l$ equals to $s$ appended with $k^2 + l^2$.  Luckily,
from the way we constructed the basic operations, this fact is obvious to Agda.
So the proof is simply the \AC{refl}exivity constructor.

On the other hand, proving that \AF{fib} matches a simpler specification that
we call \AF{fspec} requires a bit more work.
\begin{code}[hide]
module FibNonTermPf where
  open FibNonTerm
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  fspec : ℕ
        → ℕ
  fspec 0 = 1
  fspec 1 = 1
  fspec (suc (suc x)) =
       fspec (suc x)
    +  fspec x
\end{code}}
\and
\codeblock{\begin{code}
  ✔ : (s : Stack n) (x : ℕ)
    → fib (s # x) ≡ s # fspec x
  ✔ _ 0 = refl
  ✔ _ 1 = refl
  ✔ s (suc (suc x)) rewrite
    ✔ (s # suc (suc x)) (suc x) |
    ✔ (s # fspec (suc x)) x = refl
\end{code}}
\end{mathpar}
This is an inductive proof where we consider two base cases, and the
step case.  In the latter we refer to the theorem with a structurally
smaller arguments, and after rewriting such cases, the statement becomes
obvious.


\paragraph{Proving Termination}
At this point, we have seen how to write programs in the embedding, express
non-trivial properties related to the length of the stack, and verify that
a function evaluates to the same results as some other function.  One remaining
problem is that for some functions, Agda cannot automatically prove termination.
However, as long as a programmer is happy to take responsibility by putting
the annotation, we can immediately proceed to the next sections.

We demonstrate a way to prove termination of the functions from previous
sections.
%
The problem with \AF{rep} is that the recursive call happens on the stack
that became one element bigger, yet the top element decreased by one.
Therefore, this argument is not strictly structurally smaller, and there are no other
decreasing arguments, so the termination checker fails to accept this
definition.  To fix this is, we can add an extra argument on which the
function is structurally decreasing, together with a proof that it is
related in some way to the values on the stack.  For example, for
\AF{rep} we add an implicit argument \AB{k}, as well as a proof that
the top of the stack is equal to \AB{k}:

\begin{code}[hide]
module RepTerm where
    open import Data.Nat using (s≤s; z≤n)
\end{code}
\begin{code}
    rep′ : (s : Stack (2 + n)) → @0 (s ! 0 ≡ k) → Stack ((s ! 0) + n)
    rep′ {k = zero}   s@(_ # _ # zero)   refl  = s ▹ pop ▹ pop
    rep′ {k = suc m}  s@(_ # _ # suc m)  refl  =
         let  s′ = s ▹ push 1 ▹ sub ▹ index 1 ▹ exch
         in   subst-stack (+-suc _ _) (rep′ {k = m} s′ refl)

    rep : (s : Stack (2 + n)) → Stack ((s ! 0) + n)
    rep s = rep′ s refl
\end{code}
As the function is pattern-matching on the top of the stack, and the
only value of the \AD{\_≡\_} type is \AC{refl}, the argument \AB{k}
has to be \AN{zero} in the first case, and \AC{suc} \AB{m} in the second
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
as is.  The problem is that after the first recursive call \AF{fib}
\AB{s\#x\#x-1} we obtain (conceptually) a new stack.  To call \AF{fib}
on $x - 2$ we first apply \AF{exch} to the result of the first recursive call
(to bring \AB{x} at the top).  However, the termination checker does not see that \AF{fib} only
modified the top element of the stack and did not touch other elements.
While we can prove termination of the current version of \AF{fib}, due to
space limitations, we provide an alternative (terminating) implementation
of \AF{fib} in \secref{for-loop}.

\begin{comment}
There is a number of ways we can fix this, but for presentatoinal purposes
we show the shortest one.  We adjust the structure of our recursion,
so that we deal with three elements per iteration, implementing a
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
         → @0{s ! 2 ≡ k}
         → Stack (3 + n)
    fib3 {k = .0}     s@(_ # 0        # a # b) {refl} = s
    fib3 {k = .suc k} s@(_ # (suc m)  # a # b) {refl} =
      let s#1+m#a#b    = s
          s#1+m#b#a+b  = s#1+m#a#b   ▹ exch ▹ index 1 ▹ add
          s#a+b#b#m    = s#1+m#b#a+b ▹ rot3 ▹ push 1 ▹ sub
          s#m#b#a+b    = s#a+b#b#m   ▹ rot3
      in  fib3 {k = k} s#m#b#a+b {refl}

    fib : Stack (1 + n) → Stack (1 + n)
    fib s =
      let s#m#1#1              = s ▹ push 1 ▹ push 1
          s#0#fib[m]#fib[1+m]  = fib3 s#m#1#1 {refl}
      in  s#0#fib[m]#fib[1+m] ▹ pop ▹ exch ▹ pop
\end{code}
Then \AF{fib3} is doing the iteration; \AF{fib} sets the inital seed
and cleans-up the stack.  We defined a new stack operation
called \AF{rot3} that reverses the top three elements of the stack.
Note that this is not a built-in operation of PostScript, but it is
trvial to implement it in terms of \AF{roll} and \AF{exch}.
\end{comment}

\subsection{For Loop} \label{sec:for-loop}
The final part of our embedding is the for-loop construct.  Not only
this is often found in real PostScript documents, it also helps
to avoid the problem with proving termination.  The difficulty with
encoding the for-loop behaviour lies in its potential ability to
arbitrarily modify stack at every iteration.  While there is no
technical problem to encode such a behaviour in Agda, it would be
quite inconvenient to work with.  Every time one needs to ensure
that a stack returned by a for-loop contains enough elements, a
potentially complex proof has to be given.  We make our life
easier by working with a simpler version of the for loop that assumes
the same stack size at each iteration, which is sufficient for our
examples. Concretely, the boundaries
of the loop are given by two numbers $s$ and $e$, where
the loop iterates through indices $s, 1+s, \dots, e$.

We define for-loop as a function of two arguments: the body
of the for-loop given by a function and the initial stack.
\begin{code}
for : (Stack (1 + n) → Stack n) → Stack (2 + n) → Stack n
for {n} f (st # s # e) = if s ≤ e then loop (e - s) st else st
  where  loop : ℕ → Stack n → Stack n
         loop zero     st = st ▹ push s ▹ f
         loop (suc i)  st = st ▹ loop i ▹ push (suc i + s) ▹ f
\end{code}
The initial stack contains 2 loop boundary elements and $n$ other
elements. The implementation of \AF{for} computes the number of iterations \AB{i} and unrolls the
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

Now we are ready to define our \AF{fib} example using \AF{for}:
\begin{code}
fib-for : Stack (1 + n) → Stack (1 + n)
fib-for s@(_ # x) =
  s ▹ push 1 ▹ exch ▹ push 1 ▹ exch ▹ push 1 ▹ exch
    ▹ for (λ s → s ▹ pop ▹ exch ▹ index 1 ▹ add) ▹ pop
\end{code}
Our initial stack contains the function argument $x$ at the top. We modify
the stack by inserting $1$ and $1$ (inital fibonacci seeds) and $1$ (the lower bound for the for loop) before $x$.  In the function body, we remove the iteration value,
and modify $\langle a , b\rangle$ into $\langle b , a+b\rangle$.
Note that termination of \AF{fib-for} is derived automatically.
%Note that we start from 0 1 and not 1 1, as the loop goes from 0 to $x$
%inclusively.  Alternatively, we could have conditionalise on $x$.
\begin{code}[hide]
module Sierpinski where
\end{code}

We now consider a more realistic PostScript example that generates an
image of Sierpinski fractal.  The structure of the code
consists of a doubly-nested for loop that draws
a dot at each coordinate $(i,j)$ where the bit-wise `and' of $i$ and
$j$ is zero.
%
For this example we assume that a drawing function and bit-wise `and'
are already defined in PostScript, so we postulate them in Agda.  This
means that we only provide a type signature of the functions, but not
the implementation.
%
We implement conditional drawing via the helper function \AF{draw-if}.
\begin{code}
    postulate draw-circ-xy : Stack (2 + n) → Stack n
              bit-and : Stack (2 + n) → Stack (1 + n)

    draw-if : Stack (3 + n) → Stack (2 + n)
    draw-if s@(_ # 0)  = s  ▹ pop ▹ index 1 ▹ index 1 ▹ draw-circ-xy
    draw-if s          = s  ▹ pop
\end{code}
The main function sets the boundaries for both for-loops, applies
\AF{bit-and} to $i$ and $j$, and calls the drawing function, ensuring
that no extra arguments are left on the stack.
\begin{code}
    sierpinski : Stack (1 + n) → Stack n
    sierpinski s  =
      s ▹ push 0 ▹ index 1
        ▹ for (λ s → s ▹ push 0 ▹ index 2
                       ▹ for (λ s → s ▹ index 1 ▹ index 1
                                      ▹ bit-and ▹ draw-if ▹ pop)
                       ▹ pop)
        ▹ pop
\end{code}
In the implementation of algorithms like this one, it is easy to forget to
remove or copy an element within for-loops when implementing such
a code manually.  The strict stack size discipline that we have in Agda
helps to avoid these errors.

