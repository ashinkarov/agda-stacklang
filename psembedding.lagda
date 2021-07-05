\begin{code}[hide]

module psembedding where

open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_) renaming (_∸_ to _-_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit

open import Function using (case_of_; flip)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

infixl 5 _#_

variable
  X Y Z : Set
  S : Set
  M : Set → Set
  @0 k l m n : ℕ

infixl 5 _&_

_&_ : X → (X → Y) → Y
x & f = f x
{-# INLINE _&_ #-}

\end{code}

% PostScript Language and its embedding
\section{PostScript and its embedding in Agda}

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
body of the function) and the `def' command.  The definition may be
used as a regular command, including the case when it is called
recursively.  In the body of the function we check whether the argument
(the top most stack element) is zero, in which case we remove the argument
from the stack and put value one.  Otherwise, we duplicate the argument,
substract one, make a recursive call, and multiply the result with the
original argument.  Conditinoal is expressed with ifelse command,
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
transfrerable to other stack-based languages such as Forth.

\todo[inline]{More work is needed here}

\paragraph{Embedding}

Our Agda embedding defines a stack type and a number of baic operators
operating on it.

\begin{code}
data Stack (X : Set) : @0 ℕ → Set where
  []  : Stack X 0
  _#_ : Stack X n → X → Stack X (suc n)
\end{code}

\begin{code}[hide]
hd : ∀ {X n} → Stack X (1 + n) → X
hd (_ # x) = x

tl : ∀ {X n} → Stack X (1 + n) → Stack X n
tl (xs # _) = xs
\end{code}

The base operators look as follows:
\begin{code}
push : X → Stack X n → Stack X (1 + n)
push x xs = xs # x

pop : Stack X (1 + n) → Stack X n
pop (xs # x) = xs

dup : Stack X (suc n) → Stack X (suc (suc n))
dup (xs # x) = xs # x # x

exch : Stack X (2 + n) → Stack X (2 + n)
exch (xs # x # y) = xs # y # x

clear : Stack X n → Stack X 0
clear _ = []

count : Stack ℕ n → Stack ℕ (1 + n)
count xs = xs # go xs
  where
    go : Stack X n → ℕ
    go [] = 0
    go (xs # _) = suc (go xs)

binop : (X → X → X) → Stack X (2 + n) → Stack X (1 + n)
binop f (xs # x # y) = xs # f x y

add sub mul eq gt : Stack ℕ (2 + n) → Stack ℕ (1 + n)
add  = binop _+_
sub  = binop _-_
mul  = binop _*_
eq   = binop (λ x y → if x ℕ.≡ᵇ y then 1 else 0)
gt   = binop (λ x y → if x ℕ.≤ᵇ y then 0 else 1)
\end{code}


Note that nothing in this shallow embedding prevents us from doing
operations that are illegal in PostScript, such as duplicating the
whole stack or discarding it altogether. Such properties could be
enforced by using an (indexed) monad for stack operations, or by
working in a quantitative type theory such as Idris 2~\cite{TODO}.
Here we take a more straightforward approach by simply rejecting these
illegal programs in our extractor.

This function does nothing to the stack but it introduces
a bunch of runtime irrelevant argumetns.

\begin{code}
stack-id : (s : Stack ℕ 1) → {@0 b : m ℕ.> 0} → Stack ℕ 1
stack-id xs@(t # h) = (t # h)
\end{code}

These two functions demonstrate a trivial case when one function
calls another function.

\begin{code}
add1 : Stack ℕ (1 + n) → Stack ℕ (1 + n)
add1 xs = add (push 1 xs)

dblsuc : Stack ℕ (1 + n) → Stack ℕ (2 + n)
dblsuc xs = add1 (dup xs)
\end{code}

\begin{code}
sqsum : Stack ℕ (2 + n) → Stack ℕ (1 + n)
sqsum s@(_ # a # b) = s & dup & mul & exch & dup & mul & add
\end{code}

\begin{code}
subst-stack : @0 m ≡ n → Stack X m → Stack X n
subst-stack refl xs = xs
\end{code}

\begin{code}
index : (k : ℕ) → @0 k ℕ.< m → Stack X m → Stack X (1 + m)
index k k<m xs = xs # get-index k k<m xs
  where
    get-index : (k : ℕ) (@0 _ : k ℕ.< m) → Stack X m → X
    get-index zero    (ℕ.s≤s k<m) (xs # x) = x
    get-index (suc k) (ℕ.s≤s k<m) (xs # x) = get-index k k<m xs
\end{code}



The \AgdaFunction{rep} function is the simplest example of
using dependent types in a stack function.  Calling \AgdaFunction{rep} on a stack with values $x$ and $n$
replicates $x$ $n$ times, so we obtain a stack with $n$ copies of $x$.

\begin{code}
module RepSimple where
    {-# TERMINATING #-}
    rep : (s : Stack ℕ (2 + n)) → Stack ℕ (hd s + n)
    rep {n} xs@(_ # _ # zero)      = pop (pop xs)
    rep {n} xs:x:m+1@(_ # _ # suc m) =
           let
             xs:x:m   : Stack ℕ (2 + n)
             xs:x:m   = sub (push 1 xs:x:m+1)
             xs:x:m:x : Stack ℕ (3 + n)
             xs:x:m:x = index 1 (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)) xs:x:m
             xs:x:x:m : Stack ℕ (3 + n)
             xs:x:x:m = exch xs:x:m:x
           in subst-stack (+-suc _ _) (rep xs:x:x:m)
\end{code}

\begin{code}

module RepTerm where
    rep′ : (s : Stack ℕ (2 + n)) → {@0 _ : hd s ≡ k} → Stack ℕ (hd s + n)
    rep′ {n} xs@(_ # _ # zero)      = pop (pop xs)
    rep′ {n} {suc k} xs:x:m+1@(_ # _ # suc m) { refl } = let
             xs:x:m   = sub (push 1 xs:x:m+1)
             xs:x:m:x = index 1 (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)) xs:x:m
             xs:x:x:m = exch xs:x:m:x
           in subst-stack (+-suc _ _) (rep′ {k = k} xs:x:x:m {refl})

    rep : ∀ {n} → (s : Stack ℕ (2 + n)) → Stack ℕ (hd s + n)
    rep s = rep′ s {refl}

\end{code}
