
\begin{code}[hide]
open import Category.Monad

open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_)
open import Data.Char as C using (Char)
open import Data.Fin as F using (Fin; zero; suc; fromℕ<)
open import Data.List as L using (List; []; _∷_; _++_; [_]; reverse)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_) renaming (_∸_ to _-_)
open import Data.Nat.Properties
open import Data.Nat.Show using () renaming (show to showNat)
open import Data.Product
open import Data.String as S using (String; _≈?_; lines)
open import Data.Unit
open import Data.Vec as V using (Vec; []; _∷_)

open import Function using (id; case_of_; flip)

open import Level using (Level) renaming (zero to lzero; suc to lsuc)

open import Reflection as R using (TC; Name; Names)
open import Reflection.Term
open import Reflection.Literal
open import Reflection.Pattern
open import Reflection.Argument
open import Reflection.Argument.Information
open import Reflection.Argument.Modality
open import Reflection.Argument.Relevance
open import Reflection.Argument.Visibility
open import Reflection.Argument.Quantity
open import Reflection.Definition
open import Reflection.Show
import      Reflection.Name as RN
import      Reflection.TypeChecking.Monad.Syntax as R
open import Agda.Builtin.Reflection as R
  using (withReconstructed; dontReduceDefs; onlyReduceDefs)

open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)


-- Debug
open import ReflHelper
--open import Agda.Builtin.Reflection

open import psembedding

-- Check if there exists an element in the list that satisfies the predicate P.
elem : {P : X → Set} → Decidable P → List X → Bool
elem P? [] = false
elem P? (x ∷ xs) with P? x
... | yes _ = true
... | no  _ = elem P? xs

infixr 10 _<>_

_<>_ : String → String → String
_<>_ = S._++_

_<>ₜ_ : String → Term → String
s <>ₜ t = s <> showTerm t

intercalate : (delim : String) → List String → String
intercalate d [] = ""
intercalate d (x ∷ []) = x
intercalate d (x ∷ xs) = x <> d <> intercalate d xs

unlines : List String → String
unlines = intercalate "\n"

prettyName : Name → String
prettyName f = maybe id "" (L.last (S.wordsBy ('.' C.≟_) (showName f)))
\end{code}


\section{Extraction} \label{sec:extraction}

In this section, we show a concrete example of an extractor
implemented using reflection in Agda.

\paragraph{Assumptions}
Our extractor serves a dual purpose.  On the one hand, we traverse Agda
terms and map basic stack operations such as \AF{dup} and \AF{add} to their
PostScript counterparts.  On the other hand, the extractor determines
which terms are valid in the presented shallow embedding: these
are the terms that are accepted by our extractor.
Our criteria of acceptable embeddings are as follows:
\begin{itemize}
    \item The function acts on a single stack argument and returns stack.
    The function can accept arbitrary number of additional arguments
    (for verification purposes) as long as these arguments are
    computationally irrelevant.  This is checked by the function
    \AF{extract-type}.

    \item Within the function, the stack is never duplicated, discarded
    or modified by any means but embedded stack operations.  This is
    ensured by the functions \AF{extract-term} and \AF{stack-ok}.

    \item Conditionals for stack elements are implemented using
    pattern-matching.  The extractor needs to translate these patterns to
    conditional statements. This is done by %the functions
    \AF{extract-pattern} and \AF{extract-clauses}.
\end{itemize}


\subsection{Target syntax}

In the end, the extractor outputs the PostScript syntax as a plain
string. However, it is useful to work with a basic abstract syntax
representation as an intermediate stage:

\begin{code}
data PsCmd : Set where
  Pop Dup Exch Add Mul Eq Ge And : PsCmd
  Push Index : ℕ → PsCmd
  FunCall    : String → PsCmd
  For        : List PsCmd → PsCmd
  IfElse     : List PsCmd → List PsCmd → PsCmd
  FunDef     : String → List PsCmd → PsCmd
\end{code}
\begin{code}[hide]
  Rot3 : PsCmd
\end{code}

We implement a basic pretty-printer for sequences of PostScript
commands that we omit here.

\begin{code}
print-ps : List PsCmd → String
\end{code}

\begin{code}[hide]
indent : ℕ → String
indent n = intercalate "" (L.replicate n "  ")

lexpr-to-string : (ind : ℕ) → List PsCmd → List String

expr-to-string : (ind : ℕ) → PsCmd → String
expr-to-string ind (Push x) = showNat x
expr-to-string ind Dup = "dup"
expr-to-string ind Add = "add"
expr-to-string ind Mul = "mul"
expr-to-string ind Eq = "eq"
expr-to-string ind Ge = "ge"
expr-to-string ind And = "and"
expr-to-string ind Pop = "pop"
expr-to-string ind Exch = "exch"
expr-to-string ind Rot3 = "3 1 roll exch"
expr-to-string ind (For xs) = "\n"
                           <> indent ind <> "1 exch\n" -- adding step
                           <> indent ind <> "{\n"
                           <> indent (1 + ind) <> intercalate " " (lexpr-to-string (1 + ind) xs) <> "\n"
                           <> indent ind <> "} for\n"
expr-to-string ind (FunDef n xs) = indent ind <> "/" <> n <> " {\n"
                                <> indent (1 + ind) <> intercalate " " (lexpr-to-string (1 + ind) xs) <> "\n"
                                <> indent ind <> "} def\n"
expr-to-string ind (Index x) = showNat x <> " index"
expr-to-string ind (FunCall x) = x
expr-to-string ind (IfElse xs ys) = "\n"
                                 <> indent ind <> "{\n"
                                 <> indent (1 + ind) <> intercalate " " (lexpr-to-string (1 + ind) xs) <> "\n"
                                 <> indent ind <> "}\n"
                                 <> indent ind <> "{\n"
                                 <> indent (1 + ind) <> intercalate " " (lexpr-to-string (1 + ind) ys) <> "\n"
                                 <> indent ind <> "} ifelse\n"

lexpr-to-string ind [] = []
lexpr-to-string ind (x ∷ xs) = expr-to-string ind x ∷ lexpr-to-string ind xs

print-ps es = intercalate "\n" (reverse (L.map (expr-to-string 0) es))
\end{code}


\subsection{The extraction monad}

We make use of a monad for extraction to keep track of the current
state of functions that still need to be extracted, and for
propagating errors.

\begin{code}[hide]
-- This is a `Maybe`-like data type except that nothing
-- is extended with a string argument, to carry around the error.
data Err {a} (A : Set a) : Set a where
  error : String → Err A
  ok    : A → Err A

-- The state used at the top-most and term-level extraction.
record ExtractState : Set where
  constructor mkExtractState
  field
    noinline : Names   -- Functions that should not be inlined.
    todo     : Names   -- Functions to extract.
    done     : Names   -- Functions that we have processed.
\end{code}

\begin{code}
record ExtractM (X : Set) : Set where -- ...
\end{code}
\begin{code}[hide]
  field
    runExtractM : ExtractState
                → TC (ExtractState × Err X)
\end{code}

The monad structure is given by the monadic operations \AF{>>=} and
\AF{return}, which are used in the desugaring of
\AK{do}-no\-ta\-ti\-on\footnote{\hrefu{https://agda.readthedocs.io/en/v2.6.2/language/syntactic-sugar.html\#do-notation}{agda.readthedocs.io/en/v2.6.2/language/syntactic-sugar.html\#do-notation}}.  The \AF{fail} function aborts the extraction process.
\begin{code}
return : X → ExtractM X
_>>=_ : ExtractM X → (X → ExtractM Y) → ExtractM Y
fail : String → ExtractM X
\end{code}

The monad also provides two operations for managing the queue of
functions to be extracted: \AF{mark-todo} adds a function name to the
queue, while \AF{get-next-todo} returns the next function that has been
marked for extraction and has not been processed already, as long as
there are any left.  Since each individual function is only returned
at most once by \AF{get-next-todo}, we avoid extracting the same
function twice.

\begin{code}
mark-todo      : Name → ExtractM ⊤
get-next-todo  : ExtractM (Maybe Name)
\end{code}

Finally, the monad provides two operations for getting normalized types
and definitions of a given symbol. This can be used for example for
inlining Agda functions that cannot be translated to PostScript, or
for applying domain-specific optimizations through the use of rewrite
rules (\secref{partial-evaluation}).

\begin{code}
get-normalised-type : Name → ExtractM Type
get-normalised-def  : Name → ExtractM Definition
\end{code}

%The implementation of these operations is standard so we omit it here.

\begin{code}[hide]
open ExtractM

return x .runExtractM s = R.return (s , ok x)
_>>=_ m f .runExtractM s =
  runExtractM m s R.>>= λ where
    (s' , ok x)    → runExtractM (f x) s'
    (s' , error s) → R.return (s' , error s)

_>>_ : ExtractM X → ExtractM Y → ExtractM Y
m1 >> m2 = m1 >>= λ _ → m2

_<$>_ : (X → Y) → ExtractM X → ExtractM Y
f <$> m = m >>= λ x → return (f x)

fail err .runExtractM s = R.return (s , error err)

infix 0 _update-err_

_update-err_  : ExtractM X → String → ExtractM X
(m update-err err1) .runExtractM s = m .runExtractM s R.>>= λ where
  (s' , ok x)      → R.return (s' , ok x)
  (s' , error err2) → R.return (s' , error (err1 <> "\n" <> err2))

lookup-arg : List (Arg X) → ℕ → ExtractM X
lookup-arg []       _        = fail "lookup-arg: index out of range"
lookup-arg (a ∷ as) 0        = return (unArg a)
lookup-arg (a ∷ as) (suc i)  = lookup-arg as i

unless : Bool → ExtractM ⊤ → ExtractM ⊤
unless true  m = return _
unless false m = m

get-state : ExtractM ExtractState
get-state .runExtractM s = R.return (s , ok s)

modify-state : (ExtractState → ExtractState) → ExtractM ⊤
modify-state f .runExtractM s = R.return (f s , ok _)

set-state : ExtractState → ExtractM ⊤
set-state s = modify-state (λ _ → s)

is-done       : Name → ExtractM Bool
is-done f = do
  done ← ExtractState.done <$> get-state
  return (elem (f RN.≟_) done)

mark-done   : Name → ExtractM ⊤
mark-todo f = modify-state λ st → record st { todo = ins f (ExtractState.todo st) }
  where
    ins : Name → List Name → List Name
    ins f [] = [ f ]
    ins f (g ∷ gs) = if does (f RN.≟ g) then g ∷ gs else g ∷ ins f gs

mark-done f = modify-state λ st → record st { done = f ∷ ExtractState.done st }

get-next-todo = do
  todo ← ExtractState.todo <$> get-state
  go todo
  where
  go : List Name → ExtractM (Maybe Name)
  go [] = return nothing
  go (f ∷ fs) = do
    modify-state λ st → record st { todo = fs }
    done ← is-done f
    if done
      then go fs
      else do
        mark-done f
        return (just f)

liftTC       : TC X → ExtractM X
liftTC m .runExtractM s = m R.>>= λ x → R.return (s , ok x)

get-normalised-type f = do
  ty   ← liftTC (R.getType f)
  noinline ← ExtractState.noinline <$> get-state
  liftTC (withReconstructed (dontReduceDefs noinline (R.normalise ty)))

normalise-clause : Names → Clause → TC Clause
normalise-clause noinline (clause tel ps t) =
  let ctx = L.reverse (L.map proj₂ tel) in
  clause tel ps R.<$> R.inContext ctx (R.dontReduceDefs noinline (R.normalise t))
normalise-clause extern c = R.return c

normalise-clauses : Names → List Clause → TC (List Clause)
normalise-clauses noinline [] = R.return []
normalise-clauses noinline (c ∷ cs) =
  _∷_ R.<$> normalise-clause noinline c R.<*> normalise-clauses noinline cs

normalise-def : Names → Definition → TC Definition
normalise-def noinline (function cs) = function R.<$> normalise-clauses noinline cs
normalise-def noinline deff = R.return deff

get-normalised-def f = do
  deff ← liftTC (withReconstructed (R.getDefinition f))
  noinline ← ExtractState.noinline <$> get-state
  liftTC (withReconstructed (normalise-def noinline deff))
\end{code}


\subsection{The extractor}

The extractor itself consists of four functions that traverse the
different parts of the reflected Agda syntax and translate it to
PostScript commands.
In the remainder of this section, we explain the implementation of
these functions in detail.
\begin{code}[hide]
{-# TERMINATING #-}
extract-term     : Term → Pattern → ExtractM (List PsCmd)
extract-type     : Type → ExtractM ℕ
extract-clauses  : Clauses → ℕ → ExtractM (List PsCmd)
extract-def      : Name → ExtractM (List PsCmd)
\end{code}

\begin{code}[hide]
pattern `zero   = con (quote ℕ.zero) []
pattern `suc n  = con (quote ℕ.suc) (vArg n ∷ [])
pattern `num n  = lit (nat n)

pattern vArg0 x = arg (arg-info visible (modality _ quantity-0)) x
pattern hArg0 x = arg (arg-info hidden (modality _ quantity-0)) x
pattern erasedArg x = arg (arg-info _ (modality _ quantity-0)) x

pattern `Stack n    = def (quote Stack) (vArg0 n ∷ [])
pattern _`#_ x y    = con (quote Stack._#_) (_ ∷ vArg x ∷ vArg y ∷ [])

pattern `push n s  = def (quote push) (_ ∷ vArg n ∷ vArg s ∷ [])
pattern `pop s     = def (quote pop) (_ ∷ vArg s ∷ [])
pattern `dup s     = def (quote dup) (_ ∷ vArg s ∷ [])
pattern `exch s    = def (quote exch) (_ ∷ vArg s ∷ [])
pattern `rot3 s    = def (quote rot3) (_ ∷ vArg s ∷ [])

pattern `add s  = def (quote add) (_ ∷ vArg s ∷ [])
pattern `sub s  = def (quote sub) (_ ∷ vArg s ∷ [])
pattern `mul s  = def (quote mul) (_ ∷ vArg s ∷ [])
pattern `eq s   = def (quote eq) (_ ∷ vArg s ∷ [])
pattern `gt s   = def (quote gt) (_ ∷ vArg s ∷ [])

pattern `index k s = def (quote index) (_ ∷ vArg k ∷ _ ∷ vArg s ∷ [])
pattern `subst-stack s = def (quote subst-stack) (_ ∷ _ ∷ _ ∷ vArg s ∷ [])
pattern `for x y = def (quote for) (_ ∷ vArg x ∷ vArg y ∷ [])
\end{code}

\begin{code}[hide]
check-all-erased : List (Arg X) → ExtractM ⊤
check-all-erased [] = return _
check-all-erased (hArg0 _ ∷ args) = check-all-erased args
check-all-erased (_ ∷ _) = fail "..."
\end{code}

\begin{code}[hide]
stack-ok : Pattern → Term → ExtractM Bool
\end{code}


\paragraph{Extracting terms}
\AF{extract-term} traverses an Agda term and translates it to a
list of PostScript commands. For example, $\AF{add}\ (\AF{push}\ \AN{1}\ \AB{s})$ is translated to $\AC{Push}\ \AN{1}\ \AC{∷}\
\AF{Add}\ \AC{∷}\ \AC{[]}$. It takes an additional argument of type
\AD{Pattern} to check that the stack used in the expression
(in this case \AB{s}) is identical to the input stack. In this way it
ensures that we do not manipulate the stack in arbitrary ways, but
only through the primitive stack operations of PostScript.

The implementation of \AF{extract-term} uses a helper function \AF{go}
to traverse the reflected Agda syntax, collecting the generated
PostScript commands in an accumulator.  Note that we defined a number
of pattern synonims such as \AC{`pop}, \AC{`dup}, \etc{}

\begin{AgdaAlign}
\begin{code}
--: Term → Pattern → ExtractM (List PsCmd)
extract-term v stackp = go v []
  where
  go : Term → List PsCmd → ExtractM (List PsCmd)
\end{code}

The cases for basic instructions are as follows:

\begin{code}
  go (`pop   x) acc = go x (Pop   ∷ acc)
  go (`dup   x) acc = go x (Dup   ∷ acc)
  go (`exch  x) acc = go x (Exch  ∷ acc)
  go (`add   x) acc = go x (Add   ∷ acc)
  go (`mul   x) acc = go x (Mul   ∷ acc)
\end{code}
\begin{code}[hide]
  go (`rot3  x) acc = go x (Rot3  ∷ acc)
  go (`eq    x) acc = go x (Eq    ∷ acc)
  -- XXX why do we call pattern `gt` and generate `Ge`?
  go (`gt    x) acc = go x (Ge    ∷ acc)
\end{code}

For the commands \AF{push} and \AF{index}, the extractor currently
only allows natural number literals \AN{0}, \AN{1}, \AN{2}, \ldots as
the argument. For any other argument the extraction is aborted by
calling the \AF{fail} function.

\begin{code}
  go (`push (`num n) x) acc = go x (Push n ∷ acc)
  go (`push k _) acc = fail ("push non-literal: " <>ₜ k)
  go (`index (`num n) x) acc = go x (Index n ∷ acc)
  go (`index k _) acc = fail ("index non-literal: " <>ₜ k)
\end{code}

\begin{code}[hide]
  go v@(s `# `num n) acc = do
    b ← stack-ok stackp v
    if b then return acc else go s (Push n ∷ acc)
\end{code}

The function \AF{subst-stack} is only needed to satisfy the Agda
typechecker, but does not have any run-time behaviour. Hence it is
erased during extraction.

\begin{code}
  go (`subst-stack x) acc = go x acc
\end{code}

To extract a \AF{for} loop, we first check that the body of the loop
is a lambda term. If that is the case, we extract the body \AB{b},
using the stack pattern (\AC{var} \AN{0}) that refers to the stack
variable bound by the lambda.  After the body of the loop function has
been extracted, we construct the \AC{For} node and continue extraction
with the expression for the initial stack $x$.
\begin{AgdaSuppressSpace}
\begin{code}
  go (`for (vLam _ b) x) acc = do
    proc ← extract-term b (var 0)
    go x (For proc ∷ acc)
\end{code}
\begin{code}[hide]
  -- Note: this case is currently only needed for extraction of the
  -- `sum-for` example, which is not shown in the paper.
  -- So we also do not show this case of the extractor.
  go (`for (def f args) x) acc = do
    check-all-erased args
    mark-todo f
    go x (For [ FunCall (prettyName f) ] ∷ acc)
\end{code}
\begin{code}
  go (`for b _) acc = fail ("invalid for body: " <>ₜ b)
\end{code}
\end{AgdaSuppressSpace}

When it reaches a defined function that is not in the set of base
functions, the extraction proceeds in three steps. First, it adds the
function to the queue for later extraction using \AF{mark-todo}. Next,
it gets the type of the function and calls \AF{extract-type} to
determine the index of its principal argument. Finally, it looks up
the corresponding argument in the argument list and continues
extraction with that argument.

\begin{code}
  go (def f args@(_ ∷ _)) acc = do
    mark-todo f
    ty  ← get-normalised-type f
    n   ← extract-type ty
    a   ← lookup-arg args n
    go a (FunCall (prettyName f) ∷ acc)
\end{code}

After traversing through the stack operations, we reach the stack
itself. Here we check that the stack that is used is the same
as the input stack, which is done by \AF{stack-ok} (explained below).
If the check succeeds, we return the list of commands collected in
\AB{acc}.

\begin{code}
  go v acc = do
    b ← stack-ok stackp v
    if b then (return acc)
         else (fail ("stack mismatch: "
                     <> showPattern stackp <> " and " <>ₜ v))
\end{code}

The function \AF{stack-ok} ensures that when we use the stack (of type
\AD{Term}), it is identical to the stack that we got as the input to
the function (of type \AD{Pattern}). In addition to the cases below,
there are a few other cases for dealing with natural number literals
\AN{0}, \AN{1}, \AN{2}, \ldots (not shown here).


\begin{AgdaSuppressSpace}
\begin{code}
--: Pattern → Term → ExtractM Bool
stack-ok p@(p₁ `# p₂) t@(t₁ `# t₂) = do
  ok₁ ← stack-ok p₁ t₁
  ok₂ ← stack-ok p₂ t₂
  return (ok₁ ∧ ok₂)
stack-ok (var x) (var y [])  = return (x ℕ.≡ᵇ y)
stack-ok `zero     `zero     = return true
stack-ok (`suc x)  (`suc y)  = stack-ok x y
\end{code}

\begin{code}[hide]
stack-ok (`num x) (`num y) = return (x ℕ.≡ᵇ y)

stack-ok x (`num y) = do
  x′ ← pattern-to-nat x
  return (x′ ℕ.≡ᵇ y)
  where
    pattern-to-nat : Pattern → ExtractM ℕ
    pattern-to-nat `zero     = return 0
    pattern-to-nat (`suc x)  = suc <$> pattern-to-nat x
    pattern-to-nat _         = fail "not a suc/zero pattern"

stack-ok (`num x) y = do
  y′ ← term-to-nat y
  return (x ℕ.≡ᵇ y′)
  where
    term-to-nat : Term → ExtractM ℕ
    term-to-nat `zero     = return 0
    term-to-nat (`suc x)  = suc <$> term-to-nat x
    term-to-nat _         = fail "stack-ok: not a suc/zero term"
\end{code}

\begin{code}
stack-ok p t = return false
\end{code}

\end{AgdaSuppressSpace}


\paragraph{Extracting types}
The function \AF{extract-type} defines
what Agda types are valid for functions in the embedding.
It traverses an Agda type and checks that it
takes one principal argument of type \AD{Stack} and returns a value of
type \AD{Stack}. In addition, it checks that all non-principal
arguments to the function are marked as runtime-irrelevant and can
thus safely be erased during extraction. If these checks succeed, it
returns the position of the principal argument.

\begin{code}
--: Type → ExtractM ℕ
extract-type x = go x false 0
  where
  go : Type → (st-arg : Bool) → (idx : ℕ) → ExtractM ℕ
  go (Π[ s ∶ vArg (`Stack n) ] ty) false i = go ty true i
  go (Π[ s ∶ erasedArg _ ] ty) b i = go ty b (if b then i else 1 + i)
  go (`Stack n) true i = return i
  go t _ _ = fail ("invalid type: " <>ₜ t)
\end{code}


\paragraph{Extracting clauses}

\AF{extract-clauses} takes as input the cla\-uses of a function
definition and the position of the principal argument (as computed by
\AF{extract-type}) and translates the clauses to a list of PostScript
commands. For example, consider the function \AF{non-zero}:
\begin{code}
non-zero : Stack (1 + n) → Stack (1 + n)
non-zero s@(_ # 0) = s
non-zero s@(_ # _) = s ▹ pop ▹ push 1
\end{code}
The clauses of \AF{non-zero} are translated to a conditional
expression in PostScript that checks whether the top element is zero:
\begin{lstlisting}[language=PostScript]
  0 index 0 eq { } { pop 1 } ifelse
\end{lstlisting}

The two helper functions \AF{extract-natp} and \AF{extract-stackp}
extract a boolean condition from a given Agda pattern. First,
\AF{extract-natp} compiles a pattern of type \AD{ℕ} to \AC{just} a
condition on the given position on the stack, or \AC{nothing} if the
pattern matches unconditionally. There are three cases:

\begin{itemize}
\item A variable pattern \AB{n} matches any input, so \AC{nothing} is returned.
\item A closed pattern \AC{suc}\ (\AC{suc}\ (\ldots \AC{zero})) only
matches the single value equal to the number of successors, so we
return an equality check.
\item A successor pattern \AC{suc}\ (\AC{suc}\ (\ldots \AB{n}))
matches any value greater or equal to the number of successors, so we
return an inequality check.
\end{itemize}

In the implementation below, the argument \AB{c} keeps track of the
number of successors encountered so far.

\begin{code}[hide]
extract-natp  : (hd-idx : ℕ) → Pattern
              → ExtractM (Maybe (List PsCmd))
extract-stackp : (hd-idx : ℕ) → Pattern
               → ExtractM (Maybe (List PsCmd))
\end{code}
\begin{code}
--: ℕ → Pattern → ExtractM (Maybe (List PsCmd))
extract-natp hd-idx p = go p 0
  where
  mk-cmp : PsCmd → ℕ → List PsCmd
  mk-cmp cmp n = Index hd-idx ∷ Push n ∷ cmp ∷ []

  go : Pattern → ℕ → ExtractM (Maybe (List PsCmd))
  go (var _)   0 = return nothing
  go (var _)   c = return (just (mk-cmp Ge c))
  go `zero     c = return (just (mk-cmp Eq c))
  go (`suc p)  c = go p (1 + c)
  go (`num n)  c = return (just (mk-cmp Eq (c + n)))
  go p         c = fail ("not a nat: " <> showPattern p)
\end{code}

Second, the function \AF{extract-stackp} compiles a pattern of type
\AD{Stack} to \AC{just} the condition as a list of PostScript
commands, or \AC{nothing} in case the pattern is guaranteed to match.
There are two cases:
\begin{itemize}
\item A variable pattern \AB{s} matches any input, so
\AC{nothing} is returned.
\item A stack pattern \AB{ps} \AC{\#} \AB{p} matches if the top of the
stack matches \AB{p} and the remainder matches \AB{ps}.  In case both
patterns require non-trivial conditions, we combine both using the
\AC{And} instruction.
\end{itemize}

\begin{AgdaSuppressSpace}
\begin{code}
--: ℕ → Pattern → ExtractM (Maybe (List PsCmd))
extract-stackp hd-idx  (var x)    = return nothing
extract-stackp hd-idx  (ps `# p)  = do
  ml₁  ← extract-natp hd-idx p
  ml₂  ← extract-stackp (offset ml₁ + hd-idx) ps
  return (combine ml₁ ml₂)
  where
\end{code}
\begin{code}[hide]
    offset : Maybe X → ℕ
    combine  : Maybe (List PsCmd) → Maybe (List PsCmd)
             → Maybe (List PsCmd)
\end{code}
\begin{code}
    offset nothing   = 1
    offset (just _)  = 2
    combine nothing    ml₂        = ml₂
    combine ml₁        nothing    = ml₁
    combine (just l₁)  (just l₂)  = just (l₁ ++ l₂ ++ [ And ])
extract-stackp _       p =
  fail ("invalid stack pattern" <> showPattern p)
\end{code}
\end{AgdaSuppressSpace}

We are now ready to implement extraction of function clauses. The
extraction of a clause \AC{clause}\ \_ \ \AB{ps}\ \AB{t} with patterns
\AB{p} and right-hand side \AB{t} proceeds by first looking up the
pattern \AB{stackp} corresponding to the principal argument, compiling
this pattern to a condition using \AF{extract-stackp}, and (if the
condition is non-trivial) recursively extracting the remaining
clauses. The final result uses \AC{IfElse} to select the right clause.

When compiling the final clause, we skip compilation of the
pattern. This is a correct optimization because Agda enforces
completeness of definitions by pattern matching, so if the final case
is reached it is guaranteed to match.

\begin{code}
--: Clauses → ℕ → ExtractM (List PsCmd)
extract-clauses (clause _ ps t ∷ []) i = do
  stackp ← lookup-arg ps i
  extract-term t stackp
extract-clauses (clause _ ps t ∷ ts) i = do
  stackp  ← lookup-arg ps i
  just l  ← extract-stackp 0 stackp
    where nothing → extract-term t stackp
  t  ← extract-term t stackp
  ts ← extract-clauses ts i
  return (l ++ [ IfElse t ts ])
extract-clauses [] i = return []
\end{code}
\begin{code}[hide]
extract-clauses (absurd-clause _ _ ∷ cs) i =
  fail "not supported: absurd clauses"
\end{code}

\begin{comment}
Agda also has the notion of \emph{absurd clauses} that are guaranteed
to be unreachable by the coverage checker. Since they define no
run-time behaviour, we can safely skip them during
extraction. Alternatively, if we expect the extracted version of the
code to be called directly with a possibly invalid stack, we could
instead insert an assertion failure in case of an absurd clause is
reached.
\end{comment}

\paragraph{Extracting definitions}
Finally, \AF{extract-def} takes as input a (reflected) name of
an Agda function, gets its type and definition, and calls
\AF{extract-type} and \AF{extract-clauses} to translate it to a list
of PostScript commands.

\begin{code}
--: Name → ExtractM (List PsCmd)
extract-def f = do
  ty   ← get-normalised-type f
  function cs ← get-normalised-def f
    where _ → return []
  i ← extract-type ty
  b ← extract-clauses cs i
  return [ FunDef (prettyName f) b ]
\end{code}

\paragraph{Extracting whole programs}

To run the extractor on a complete Agda program, we need to run it on
the main function and all its (recursive) dependencies. This is
implemented by the function \AF{extract-defs}, which makes use of
\AF{get-next-todo} of the extraction monad to extract all function
definitions one by one. Since any Agda program has a finite number of
definitions and each definition is only processed once, this function
is terminating. However, the Agda termination checker does not detect
this, so we mark it as terminating manually using a pragma.

\begin{code}
{-# TERMINATING #-}
extract-defs : ExtractM (List PsCmd)
extract-defs = do
  just f ← get-next-todo
    where nothing → return []
  xs ← extract-def f
  ys ← extract-defs
  return (xs ++ ys)
\end{code}

We define a macro \AMA{extract} as the main entry point of the
extractor.  This macro takes as inputs the name of the main
function and a list of functions that
should not be inlined (see the next section for more
details on inlining). The implementation of the macro (not shown here)
runs \AF{extract-defs} on the initial state. If extraction succeeds,
it replaces the call to the macro by the pretty-printed result, and
otherwise throws an error.

\begin{code}[hide]
base : List Name
base = quote add ∷ quote sub ∷ quote mul
     ∷ quote eq ∷ quote gt
     ∷ quote push ∷ quote pop ∷ quote dup ∷ quote exch
     ∷ quote rot3 ∷ quote index ∷ quote subst-stack
     ∷ quote for ∷ []
\end{code}

\begin{code}
macro extract : Name → Names → Term → TC ⊤
\end{code}
\begin{code}[hide]
      extract main noinline hole =
        let initState =
              mkExtractState noinline [ main ] base in
        runExtractM extract-defs initState R.>>= λ where
          (_ , ok p)       → R.quoteTC (print-ps p) R.>>= R.unify hole
          (_ , error err)  → R.typeError [ R.strErr err ]
\end{code}

We provide a default list \AF{base} of functions for which to avoid
inlining, which can be further tailored to the extraction of a
specific program.


\paragraph{Testing the extractor}

\begin{wrapfigure}{r}{.3\columnwidth}
\epsfbox[0 0 66 66]{sierp.ps}
\caption{\label{fig:sierpinski}Draw \AF{sierpinski}.}
\end{wrapfigure}
Thanks to the theorem-proving capabilities of Agda, we can embed test
cases for the extractor as equality proofs. These test cases
are run automatically during type checking, so if a change to the
extractor causes one of them to fail it will not go unnoticed.

As an example, here is a test that \AF{add-1} is extracted
correctly. To improve readability, we use the \AF{lines} function to
split the output of the extractor into individual lines.

\begin{code}
test-add-1 : lines (extract add-1 base) ≡  ( "/add-1 {"
                                         ∷ "  1 add"
                                         ∷ "} def"
                                         ∷ [] )
test-add-1 = refl
\end{code}
We can test the output of the extractor on the other examples from the
previous section in a similar fashion.
Finally, we can feed generated programs into PostScript
interpreters and obtain outputs such as one at~\figref{sierpinski}.


\begin{code}[hide]
_ : lines (extract non-zero base) ≡
  ( "/non-zero {"
  ∷ "  0 index 0 eq "
  ∷ "  {"
  ∷ "    "
  ∷ "  }"
  ∷ "  {"
  ∷ "    pop 1"
  ∷ "  } ifelse"
  ∷ ""
  ∷ "} def"
  ∷ [] )
_ = refl

dblsuc : Stack (1 + n) → Stack (2 + n)
dblsuc xs = add-1 (dup xs)

_ : lines (extract dblsuc (quote add-1 ∷ base)) ≡
  ( "/add-1 {"
  ∷ "  1 add"
  ∷ "} def"
  ∷ ""
  ∷ "/dblsuc {"
  ∷ "  dup add-1"
  ∷ "} def"
  ∷ [] )
_ = refl

boo : Stack (1 + n) → @0 ℕ → Stack (1 + n)
boo (s # x) n = s # (0 + x)
--boo s n = add (push 1 s)
--boo s = λ n → add (push 1) s

_ : lines (extract sqsum base) ≡
  ( "/sqsum {"
  ∷ "  dup mul exch dup mul exch add"
  ∷ "} def"
  ∷ [] )
_ = refl

_ : lines (extract RepSimple.rep base) ≡
  ( "/rep {"
  ∷ "  0 index 0 eq "
  ∷ "  {"
  ∷ "    pop pop"
  ∷ "  }"
  ∷ "  {"
  ∷ "    1 sub 1 index exch rep"
  ∷ "  } ifelse"
  ∷ ""
  ∷ "} def"
  ∷ [] )
_ = refl

_ : lines (extract FibNonTerm.fib base) ≡
  ( "/fib {"
  ∷ "  0 index 0 eq "
  ∷ "  {"
  ∷ "    pop 1"
  ∷ "  }"
  ∷ "  {"
  ∷ "    0 index 1 eq "
  ∷ "    {"
  ∷ "      pop 1"
  ∷ "    }"
  ∷ "    {"
  ∷ "      dup 1 sub fib exch 2 sub fib add"
  ∷ "    } ifelse"
  ∷ ""
  ∷ "  } ifelse"
  ∷ ""
  ∷ "} def"
  ∷ [] )
_ = refl
\end{code}

\begin{comment}
As another example, we test that the implementation of \AF{fib} is
extracted correctly:

\begin{code}
_ : lines (extract Fib3.fib base) ≡
  ( "/fib3 {"
  ∷ "  2 index 0 eq "
  ∷ "  {"
  ∷ "    "
  ∷ "  }"
  ∷ "  {"
  ∷ "    exch 1 index add 3 1 roll exch"
    <> " 1 sub 3 1 roll exch fib3"
  ∷ "  } ifelse"
  ∷ ""
  ∷ "} def"
  ∷ ""
  ∷ "/fib {"
  ∷ "  1 1 fib3 pop exch pop"
  ∷ "} def"
  ∷ [] )
_ = refl
\end{code}
\end{comment}

\begin{code}[hide]
_ : lines (extract sum-for base) ≡
  ("/sum-for {" ∷
   "  10 exch 0 exch " ∷
   "  1 exch" ∷
   "  {" ∷
   "    add" ∷
   "  } for" ∷
   "" ∷
   "} def" ∷ [])
_ = refl

_ : lines (extract fib-for base) ≡
  ("/fib-for {" ∷
   "  1 exch 1 exch 1 exch " ∷
   "  1 exch" ∷
   "  {" ∷
   "    pop exch 1 index add" ∷
   "  } for" ∷
   " pop" ∷
   "} def" ∷ [])
_ = refl
\end{code}

\begin{code}[hide]
_ : lines (extract Sierpinski.sierpinski base) ≡
  ("/draw-if {" ∷
   "  0 index 0 eq " ∷
   "  {" ∷
   "    pop 1 index 1 index draw-circ-xy" ∷
   "  }" ∷
   "  {" ∷
   "    pop" ∷
   "  } ifelse" ∷
   "" ∷
   "} def" ∷
   "" ∷
   "/sierpinski {" ∷
   "  0 1 index " ∷
   "  1 exch" ∷
   "  {" ∷
   "    0 2 index " ∷
   "    1 exch" ∷
   "    {" ∷
   "      1 index 1 index bit-and draw-if pop" ∷
   "    } for" ∷
   " pop" ∷
   "  } for" ∷
   " pop" ∷
   "} def" ∷ [])
_ = refl
\end{code}

\end{AgdaAlign}
