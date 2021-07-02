\begin{code}

open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)
open import Function
open import Data.Unit

infixl 5 _,_
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
  _,_ : ∀ {n} → Stack X n → X → Stack X (suc n)
\end{code}

The base operators look as follows:
\begin{code}
dup : ∀ {X n} → Stack X (suc n) → Stack X (suc (suc n))
dup (xs , x) = xs , x , x

exch : ∀ {X n} → Stack X (2 + n) → Stack X (2 + n)
exch (xs , x , y) = xs , y , x

add : ∀ {n} → Stack ℕ (2 + n) → Stack ℕ (1 + n)
add (xs , x , y) = xs , x + y

mul : ∀ {n} → Stack ℕ (2 + n) → Stack ℕ (1 + n)
mul (xs , x , y) = xs , x * y
\end{code}
