\begin{code}[hide]

module psembedding where

open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _≤_) renaming (_∸_ to _-_)
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

PostScript is a document description language.  Besides the usual markup,
it also allows to define arbitrary computations.  It is dynamically typed
and it is stack-based. \Ie{} there is a notion of a global stack, which
is used for both, passing values and storing results.  All the commands
are argumentless operators, and a program is a chain of such commands.
For example, consider a function that computes $a^2 + b^2$ for $a$ and
$b$ being the top two values on the stack.
\begin{lstlisting}[language=PostScript]
% a b -- a*a+b*b
dup   % a b b    duplicate top element
mul   % a b*b    multiply top two numbers
exch  % b*b a    excange top two elements
dup   % b*b a a  duplicate top element
mul   % b*b a*a  multiply top two numbers
add   % b*b+a*a  add top two numbers
\end{lstlisting}

As it can be seen, commands use mnemonic names and typically implement
a simple computation or element manipulation on the stack.  Recursive
function definitions are written as follows:
\begin{lstlisting}[language=PostScript]
/fact {
  % n -- n!
  dup      % n n
  0 eq     % n 0==n
  {        % if 0==n
    pop    % empty stack
    1      % 1 [result]
  }
  {        % if !0==n
    dup    % n n
    1 sub  % n n-1
    fact   % n fac(n-1)
    mul    % n*fac(n-1) [result]
  } ifelse
} def
\end{lstlisting}
A function is defined with the slash name (fact in the above example),
followed by a block of commands that are written within braces (the
body of the function) and the \textbf{def} command.  The definition may be
used as a regular command, including the case when it is called
recursively.  In the body of the function we check whether the argument
(the top most stack element) is zero, in which case we remove the argument
from the stack and put value one.  Otherwise, we duplicate the argument,
substract one, make a recursive call, and multiply the result with the
original argument.  Conditional is expressed with an \textbf{ifelse} command,
putting two code blocks on the stack as arguments.

Finally, consider the fibonacci function:
\begin{lstlisting}[language=PostScript]
/fib {
  % n -- fib(n)
  dup dup      % n n n
  0 eq exch    % n n==0 n
  1 eq         % n n==0 n==1
  or           % n (n==0 || n==1)
  { 1 }        % [return] 1 if (n==0||n==1)
  {
    dup        % n n
    1 sub fib  % n fib(n-1)
    exch       % fib(n-1) n
    2 sub fib  % fib(n-1) fib(n-2)
    add        % fib(n-1)+fib(n-2)
  } ifelse
} def
\end{lstlisting}
And here is how we can use this function application repeatedly to draw
a picture using PostScript interpreter:

\epsfbox[0 0 200 100]{1.ps}

We have applied the fib function several times, while drawing a bar of
the corresponding height each time.

While in principle PostScript has many more operators and drawing commands,
in this paper we mostly consider it as a stack language that can define
functions on natural numbers.  We do this to keep the complexity as low
as possible, yet exposing enough operators to demonstrate the
verification.  Also, such a minimalist subset makes the example immediately
transferrable to other stack-based languages such as Forth.

\subsection{Embedding in Agda}

Our Agda embedding defines a stack type and a number of basic operators
operating on it.  A typical error that happens when programming
in stack languages directly is underflowing or overflowing the stack.  The
former is when we expect more elements on the stack than we actually have,
therefore indexing beyound the first element will cause a runtime error.
The latter is when we put more elements on the stack than it is capable to
store.  In the embedding one of our main goals is avoiding underflows,
which occur extremely often.

\paragraph{Stack type}
We define the type of our stack inductively, and we force the type to carry
the length of the corresponding stack. The stack can store elements of type
\AB{X}, which is a type parameter.
\begin{code}
data Stack (X : Set) : @0 ℕ → Set where
  []  : Stack X 0
  _#_ : Stack X n → X → Stack X (suc n)

infixl 5 _#_
\end{code}
Similarly to lists, stacks can be constructed in two ways.  Stacks of length
zero can are constructed using \AC{[]}.  Stacks of length $1 + n$ are constructed
with the append constructor \AC{\_\#\_}, where the first argument is a stack of
length $n$ and the second argument is the element of type \AB{X}.  For example,
a stack of three natural numbers can be built as follows:
\begin{code}
ex₁ : Stack ℕ 3
ex₁ = [] # 1 # 2 # 3
\end{code}
We defined \AC{\_\#\_} to be left-associative, therefore we do not put any parenthesis.

\paragraph{Basic Operations}

\begin{code}[hide]
tl : ∀ {X n} → Stack X (1 + n) → Stack X n
tl (xs # _) = xs
\end{code}

The basic stack operations are defined as functions from \AD{Stack} to \AD{Stack}.
The type index makes it possible to capture precisely the effect of each
operation.  For example:
\begin{code}
push : X → Stack X n → Stack X (1 + n)
push x xs = xs # x

pop : Stack X (1 + n) → Stack X n
pop (xs # x) = xs

dup : Stack X (suc n) → Stack X (2 + n)
dup (xs # x) = xs # x # x

exch : Stack X (2 + n) → Stack X (2 + n)
exch (xs # x # y) = xs # y # x

clear : Stack X n → Stack X 0
clear _ = []
\end{code}
As it can be seen, the nature of these operations is straight-forward.  However,
note that the length index of \AD{Stack} ensures that the body of the function
respects the specification.  If the body of the function returns the stack that
does not have the length prescribed by the type, such a function would not typecheck.

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
count : Stack ℕ n → Stack ℕ (1 + n)
count xs = xs # go xs
  where
    go : Stack X n → ℕ
    go []       = 0
    go (xs # _) = suc (go xs)
\end{code}

Finally, we define arithmetic operations:
\begin{code}
add sub mul eq gt : Stack ℕ (2 + n) → Stack ℕ (1 + n)
add (s # x # y) = s # x + y
sub (s # x # y) = s # x - y
mul (s # x # y) = s # x * y
eq  (s # x # y) = s # (if x ℕ.≡ᵇ y then 1 else 0)
gt  (s # x # y) = s # (if x ℕ.≤ᵇ y then 0 else 1)
\end{code}

%Finally, we define arithmetic operations using a helper function \AD{binop}
%that always acts on the two topmost elements of the stack.
%\begin{code}
%binop : (X → X → X) → Stack X (2 + n) → Stack X (1 + n)
%binop f (xs # x # y) = xs # f x y
%
%add sub mul eq gt : Stack ℕ (2 + n) → Stack ℕ (1 + n)
%add  = binop _+_
%sub  = binop _-_
%mul  = binop _*_
%eq   = binop (λ x y → if x ℕ.≡ᵇ y then 1 else 0)
%gt   = binop (λ x y → if x ℕ.≤ᵇ y then 0 else 1)
%\end{code}

\todo[inline]{Explain these guys below}

\begin{code}
subst-stack : @0 m ≡ n → Stack X m → Stack X n
subst-stack refl xs = xs
\end{code}

\begin{code}

get-index : (k : ℕ) (@0 _ : k ℕ.< m) → Stack X m → X
get-index zero    (ℕ.s≤s k<m) (xs # x) = x
get-index (suc k) (ℕ.s≤s k<m) (xs # x) = get-index k k<m xs

index : (k : ℕ) → @0 k ℕ.< m → Stack X m → Stack X (1 + m)
index k k<m xs = xs # get-index k k<m xs
\end{code}

\todo[inline]{Move this to section 4}
Note that nothing in this shallow embedding prevents us from doing
operations that are illegal in PostScript, such as duplicating the
whole stack or discarding it altogether. Such properties could be
enforced by using an (indexed) monad for stack operations, or by
working in a quantitative type theory such as Idris 2~\cite{TODO}.
Here we take a more straightforward approach by simply rejecting these
illegal programs in our extractor.

\subsection{Examples}

Let us demonstrate how a typical program would look like in the
proposed embedding.  Per our assumption, we need to express all the
operations in terms of the base functions defined above.  Let us
start with a trivial operation that adds one to the top element of
the stack.

\begin{code}
add-1 : Stack ℕ (1 + n) → Stack ℕ (1 + n)
add-1 s = add (push 1 s)
\end{code}

We are required to define the type, which in turn forces us to
specify how does the operation change the length of the stack.
Stack operators are regular functions, so the chain of applications
would be written in reverse, when comparing to the corresponding
PostScript program.  While this does not effect functionality,
it may be aesthetically pleasing to maintain the original order
of operators.  This can be achieved by defining a trivial Agda
operator that reverses arguments in function application.  We
call this operator \AD{\_▹\_}:

\begin{code}
infixl 5 _▹_
_▹_ : X → (X → Y) → Y
x ▹ f = f x
\end{code}
\begin{code}[hide]
-- not sure if we need to expose this in the text
{-# INLINE _▹_ #-}
\end{code}

Now we can rewrite the above example as:

\begin{code}
add-1′ : Stack ℕ (1 + n) → Stack ℕ (1 + n)
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
sqsum : Stack ℕ (2 + n) → Stack ℕ (1 + n)
sqsum s = s ▹ dup ▹ mul ▹ exch ▹ dup ▹ mul ▹ exch ▹ add
\end{code}
It can be easier to understand the code if we introduce internal
stack states as let bindings:
\begin{code}
sqsum′ : Stack ℕ (2 + n) → Stack ℕ (1 + n)
sqsum′ s:a:b = let
        s:a:b*b    = s:a:b      ▹ dup   ▹ mul
        s:b*b:a*a  = s:a:b*b    ▹ exch  ▹ dup ▹ mul
        s:a*a:b*b  = s:b*b:a*a  ▹ exch
    in s:a*a:b*b ▹ add
\end{code}
Notice that in Agda, variable/function names are chains of almost
arbitrary symbols with no spaces.

\todo[inline]{Shall we talk about verification here or in a separate chapter?}
The nature of dependently-typed systems makes it possible not only to
specify functions with ``built-in'' constraints, such as length of the stack,
but also prove some properties about existing functions as theorems.  For
example, we can prove that the above function actually implements the sum of squares:
\begin{code}
sqsum-thm : ∀ {s : Stack ℕ n}{a b}
          → sqsum (s # a # b) ≡ s # a * a + b * b
sqsum-thm = refl
\end{code}
The theorem says that for any $s$, $a$ and $b$, application of \AD{sqsum} to
$s$ appended with $a$ and $b$ equals to $s$ appended with $a^2 + b^2$.  Luckily,
from the way we constructed basic operations, this fact is obvious to Agda,
therefore, the proof is simply the \AC{refl}exivity constructor.

\paragraph{Pattern Matching}
Let us now consider a function that
computes $n$-th fibonacci number, where we use recursion
and need to conditionalise on a stack element.

\begin{code}[hide]
module FibNonTerm where
\end{code}
\begin{code}
  {-# TERMINATING #-}
  fib : Stack ℕ (1 + n) → Stack ℕ (1 + n)
  fib s@(_ # 0)             = s ▹ pop   ▹ push 1
  fib s@(_ # 1)             = s ▹ pop   ▹ push 1
  fib s@(_ # suc (suc x))   = s ▹ dup   ▹ push 1 ▹ sub ▹ fib
                                ▹ exch  ▹ push 2 ▹ sub ▹ fib
                                ▹ add
\end{code}
A standard way to conditionalise on the argument in Agda is by using
pattern-matching.  Here we have to match the structure of the stack
as well as the structure of the element, but the rest is a straight-forward
code.

We leave it as an excercise to the reader to verify that the above code
is actually computing fibonacci numbers.  We only provide a formal
proof that the \AD{fib} always computes the same element as \AD{fib-spec}
function.
\begin{code}
  fib-spec : ℕ → ℕ
  fib-spec 0 = 1 ; fib-spec 1 = 1
  fib-spec (suc (suc x)) = fib-spec (suc x) + fib-spec x

  fib-thm : (s : Stack ℕ n) (x : ℕ) → fib (s # x) ≡ s # fib-spec x
  fib-thm _ 0 = refl ; fib-thm _ 1 = refl
  fib-thm s (suc (suc x))
          rewrite  (fib-thm (s # suc (suc x)) (suc x)) |
                   (fib-thm (s # fib-spec (suc x)) x) = refl
\end{code}

While we can prove that the function computes the expected
result, Agda does not see that the \AD{fib} function terminates.
For now, we add an explicit annotation of this fact, but in the next
subsection we will demonstrate how to deal with this formally.


\paragraph{Dependent Stack Length}
So far all the specifications within the embedded langauge did not
require dependent types, and could be encoded in languages with a weaker
type system such as Haskell or OCaml.  However, it becomes very clear
that even simplest programs in stack languages may expose a dependency
between the stack argument and the stack length.  Those cases cannot
be expressed in non-dependently-typed host langauges.  A simple example
of such a program is a function \AF{rep} that replicates the $x$ value $n$ times,
where $x$ and $n$ are top two stack elements.
Here is a possible implementation of that function:

\begin{code}
hd : ∀ {X n} → Stack X (1 + n) → X
hd (_ # x) = x
\end{code}
\begin{code}[hide]
module RepSimple where
    open import Data.Nat using (s≤s; z≤n)
\end{code}
\begin{code}
    {-# TERMINATING #-}
    rep : (s : Stack ℕ (2 + n)) → Stack ℕ (hd s + n)
    rep       s@(_ # _ # zero)   = s ▹ pop ▹ pop
    rep s:x:m+1@(_ # _ # suc m)  = let
             s:x:m    = s:x:m+1  ▹ push 1 ▹ sub
             s:x:m:x  = s:x:m    ▹ index 1 (s≤s (s≤s z≤n))
             s:x:x:m  = s:x:m:x  ▹ exch
           in subst-stack (+-suc _ _) (rep s:x:x:m)
\end{code}

First, we define the \AD{hd} helper function that returns the top element
of the stack.  We use this function to specify the length of the stack
returned by \AD{rep}.  This length is the value of the top element of the
stack when entering the function the first time.  In case this argument
is zero, we remove two elements from the stack: the argument we were
replicating, and the count argument.  Otherwise, we decrease the count,
copy the argument we are replicating, and put them in the expected position
to make the next recrusive call.  The second argument to \AF{index} is a
proff that $1 < 2 + n$.  At the end we apply
\AF{subst-stack} to fit the type definition.  The length of \AF{rep} \AB{s:x:x:m}
is $(m + (1 + n))$ whereas we need the length
$(1 + (m + n))$.  Such an equality is not obvious to Agda, we
apply the \AD{+-suc} function from the standard library that translates
between these expressions.


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
    rep′ : (s : Stack ℕ (2 + n)) → @0{hd s ≡ k} → Stack ℕ (hd s + n)
    rep′ {k = .0}            s@(_ # _ # zero)  {refl}  = s ▹ pop ▹ pop
    rep′ {k = .suc k}  s:x:m+1@(_ # _ # suc m) {refl}  = let
             s:x:m    = s:x:m+1  ▹ push 1 ▹ sub
             s:x:m:x  = s:x:m    ▹ index 1 (s≤s (s≤s z≤n))
             s:x:x:m  = s:x:m:x  ▹ exch
           in subst-stack (+-suc _ _) (rep′ {k = k} s:x:x:m {refl})

    rep : (s : Stack ℕ (2 + n)) → Stack ℕ (hd s + n)
    rep s = rep′ s {refl}
\end{code}
As the function is pattern-matching on the top of the stack, and the
only value of the \AD{\_≡\_} type is \AC{refl}, the argument \AB{k}
has to be \AN{0} in the first case, and some successor in the second
case.  This trick creates ensures that \AB{k} is structurally decreasing,
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
on the same stack.  The problem is that after the first recusive call \AF{fib}
\AB{s:x:x-1} we obtain (conceptually) a new stack.  In order to call \AF{fib}
on $x - 2$ we first apply \AF{exch} to the result of the first recursive call
(to bring \AB{x} at the top).  However, we cannot prove that \AF{fib} only
modified the top element of the stack and did not touch other elements.
There is a number of ways we can fix this, but for presentatoinal purposes
we show the shortest one.  We adjust the structure of our recursion,
so that we deal with three elements per iteration, implementing a simple
scheme $\langle 1+x, a, b \rangle \leadsto \langle x, b, a+b \rangle$.
Where $x$ is the number in the sequence that we want to find, and $a = b = 1$
in the inital call:

\begin{code}
rot3 : ∀ {X}{@0 n} → Stack X (3 + n) → Stack X (3 + n)
rot3 (s # a # b # c) =  s # c # b # a
\end{code}
\begin{code}[hide]
module Fib3 where
    open import Data.Nat using (_<_; s≤s; z≤n)
    open import Function using (_$_)
\end{code}
\begin{code}
    fib3 : (s : Stack ℕ (3 + n))
         → {@0 _ : get-index 2 (s≤s (s≤s (s≤s z≤n))) s ≡ k}
         → Stack ℕ (3 + n)
    fib3 {k = .0}     s@(_ # 0        # a # b) {refl} = s
    fib3 {k = .suc k} s@(_ # (suc m)  # a # b) {refl} = let
      s:1+m:a:b    = s
      s:1+m:b:a+b  = s:1+m:a:b   ▹ exch ▹ index 1 (s≤s (s≤s z≤n)) ▹ add
      s:a+b:b:m    = s:1+m:b:a+b ▹ rot3 ▹ push 1 ▹ sub
      s:m:b:a+b    = s:a+b:b:m   ▹ rot3
      in fib3 {k = k} s:m:b:a+b {refl}

    fib : Stack ℕ (1 + n) → Stack ℕ (1 + n)
    fib s = let
      s:m:1:1              = s ▹ push 1 ▹ push 1
      s:0:fib[m]:fib[1+m]  = fib3 s:m:1:1 {refl}
      in s:0:fib[m]:fib[1+m] ▹ pop ▹ exch ▹ pop
\end{code}
Then \AF{fib3} is doing the iteration; \AF{fib} sets the inital seed
and cleans-up the stack.  We defined a new stack operation
called \AF{rot3} that reverses the top three elements of the stack.
Note that this is not a built-in operation of PostScript, but it is
trvial to implement it in terms of \AF{roll} and \AF{exch}.

\subsection{For Loop}

\todo[inline]{Deal with the code}

\begin{code}
≤-ok : ∀ {x y} → {w : True (y ≥? x)} → x ≤ y
≤-ok {w = w} = toWitness w

infixr 9 _∘~_
_∘~_ : ∀ {A B C : Set} → (A → B) → (B → C) → (A → C)
f ∘~ g = λ x → g (f x)
{-# INLINE _∘~_ #-}

-- For loop
data _≥₁_ (l : ℕ) : ℕ → Set where
  ≥-done : l ≥₁ l
  ≥-next : ∀ {m} → l ≥₁ (suc m) → l ≥₁ m

≥₁-count : ∀ {a b} → a ≥₁ b → (n : ℕ) → ℕ
≥₁-count ≥-done      n = n
≥₁-count (≥-next a≥sb) n = ≥₁-count a≥sb n + n

for : (s : Stack ℕ (2 + k + n))
      → {e≥₁s : get-index 0 ≤-ok s ≥₁ get-index 1 ≤-ok s}
      → (∀ {@0 m} → Stack ℕ (1 + k + m) → Stack ℕ (k + m))
      → Stack ℕ (k + n)
for {k}{n} (st # s # .s) {≥-done}        f = f {n} (st # s)
for {k}{n} (st # s #  e) {≥-next e≥₁1+s} f = for {k}{n} (f (st # s) # suc s # e) {e≥₁1+s} f

x≥₁sy→x≥₁y : ∀ {x y} → x ≥₁ suc y → x ≥₁ y
x≥₁sy→x≥₁y ≥-done = ≥-next ≥-done
x≥₁sy→x≥₁y (≥-next x≥sy) = ≥-next (x≥₁sy→x≥₁y x≥sy)

x≥₁y→s[x]≥₁y : ∀ {x y} → x ≥₁ y → suc x ≥₁ y
x≥₁y→s[x]≥₁y {x} {.x} ≥-done = ≥-next ≥-done
x≥₁y→s[x]≥₁y {x} {y} (≥-next x≥₁y) = ≥-next (x≥₁y→s[x]≥₁y x≥₁y)

≥₁-trans : ∀ {x y z} → x ≥₁ y → y ≥₁ z → x ≥₁ z
≥₁-trans {x} {y} {.y} x≥y ≥-done = x≥y
≥₁-trans {x} {y} {z} x≥y (≥-next y≥z) = x≥₁sy→x≥₁y (≥₁-trans x≥y y≥z)

x≥₁0 : ∀ {x} → x ≥₁ 0
x≥₁0 {zero} = ≥-done
x≥₁0 {suc x} = ≥₁-trans (≥-next ≥-done) x≥₁0

-- 10 + 0 + 1 + ... + x
sum-for : Stack ℕ (1 + n) → Stack ℕ (1 + n)
sum-for s@(_ # x) = for {k = 1}
                        (s ▹ push 10 ▹ exch ▹ push 0 ▹ exch) {x≥₁0}
                        add

-- note that we start from 0 1 here, as the loop goes from 0 to x inclusively.
-- alternatively, we could conditionalise on x
fib-for : Stack ℕ (1 + n) → Stack ℕ (1 + n)
fib-for s@(_ # x) = for {k = 2}
                        (s ▹ push 0 ▹ exch ▹ push 1 ▹ exch ▹ push 0 ▹ exch) {x≥₁0}
                        (pop ∘~ exch ∘~ index 1 ≤-ok ∘~ add)
                    ▹ pop


module Sierpinski where
    postulate
      draw-circ-xy : Stack ℕ (2 + n) → Stack ℕ n
      bit-and : Stack ℕ (2 + n) → Stack ℕ (1 + n)

    draw-if : Stack ℕ (3 + n) → Stack ℕ (2 + n)
    draw-if s@(_ # 0) = s ▹ pop ▹ index 1 ≤-ok ▹ index 1 ≤-ok
                          ▹ draw-circ-xy
    draw-if s         = s ▹ pop

    sierp : Stack ℕ (1 + n) → Stack ℕ n
    sierp s = for {k = 1}
                  (s ▹ push 0 ▹ index 1 ≤-ok) {x≥₁0}
                  (λ s → for {k = 1}
                             (s ▹ push 0 ▹ index 2 ≤-ok) {x≥₁0}
                             (index 1 ≤-ok ∘~ index 1 ≤-ok ∘~
                              bit-and ∘~ draw-if ∘~ pop)
                         ▹ pop)
              ▹ pop
\end{code}
