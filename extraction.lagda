
\begin{code}[hide]
open import Category.Monad

open import Data.Bool using (Bool; true; false; if_then_else_; not)
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
open import Agda.Builtin.Reflection as R
  using (withReconstructed; dontReduceDefs)

open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

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

intercalate : (delim : String) → List String → String
intercalate d [] = ""
intercalate d (x ∷ []) = x
intercalate d (x ∷ xs) = x <> d <> intercalate d xs

unlines : List String → String
unlines = intercalate "\n"

prettyName : Name → String
prettyName f = maybe id "" (L.last (S.wordsBy ('.' C.≟_) (showName f)))
\end{code}


\section{Extraction}

In this section, we show a concrete example of an extractor
implemented using reflection in Agda. On a basic level, the extractor
is a simple traversal of the syntax that maps basic stack operations
such as \AF{dup} and \AF{add} to their
corresponding syntax in PostScript, erases any arguments that are only
present to satisfy the Agda typechecker, and rejects any Agda code
that does not fall within the shallow embedding. However, there are a
few requirements that make the extractor slightly more complex:

\begin{itemize}

\item In a stack language such as PostScript there is a unique stack
on which all operations act. However, our shallow embedding in Agda
does not enforce that the stack is not duplicated, discarded, or
otherwise modified in arbitrary ways. The extractor thus needs to
ensure that for each definition, the stack that is used in its body is
the same as the input stack. This is done in the implementation of
\AF{extract-term} and \AF{stack-ok}.
for more details.

\item Operations on stacks can take arguments besides the `main' stack
argument, as long as these other arguments are computationally
irrelevant. The extractor thus needs to determine which argument of a
given function corresponds to the input stack, and that the other
arguments can indeed be erased. This is done by the implementation
\AF{extract-type}.

\item We allow functions on stacks to to make limited use of pattern
matching on values on the stack, as for example in the definition of
\AF{rep}. The extractor needs to translate these patterns to
conditional statements. This is done in the implementation of
\AF{extract-pattern} and \AF{extract-clauses}.

\end{itemize}


\subsection{Target syntax}

In the end, the extractor outputs the PostScript syntax as a plain
string. However, it is useful to work with a basic abstract syntax
representation as an intermediate stage:

\begin{code}
data PsCmd : Set where
  Pop Dup Exch Add Sub Mul Eq Ge And Rot3 : PsCmd
  Push     : ℕ → PsCmd
  If       : List PsCmd → PsCmd
  IfElse   : List PsCmd → List PsCmd → PsCmd
  FunDef   : String → List PsCmd → PsCmd
  Index    : ℕ → PsCmd
  FunCall  : String → PsCmd
\end{code}

We implement a basic pretty-printer for sequences of PostScript
commands, which we omit here.

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
expr-to-string ind Sub = "sub"
expr-to-string ind Exch = "exch"
expr-to-string ind Rot3 = "3 1 roll exch"
expr-to-string ind (If xs) = "\n"
                           <> indent ind <> "{\n"
                           <> indent ind <> intercalate " " (lexpr-to-string (1 + ind) xs) <> "\n"
                           <> indent ind <> "\n} if\n"
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
propagating errors. By opening the \AD{RawMonad} instance, we bring
the monadic operations \AR{>>=} and \AR{return} into scope, which
also enables \AK{do}-notation.

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
    base : Names   -- Atomic functions that we do not traverse into.
    todo : Names   -- Functions to extract
    done : Names   -- Functions that we have processed.
\end{code}

\begin{code}
record ExtractM (X : Set) : Set where
  field
    runExtractM : ExtractState
                → TC (ExtractState × Err X)
open ExtractM

monadExtractM : RawMonad ExtractM
open RawMonad monadExtractM
\end{code}

The monad provides two operations for throwing errors: \AF{fail}
throws an error, aborting the extraction, while \AF{\_update-err\_}
appends more information to the error message, or does nothing if
there is no error.

\begin{code}
fail          : String → ExtractM X
_update-err_  : ExtractM X → String → ExtractM X
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
rules (see Section \ref{TODO}).

\begin{code}
get-normalised-type : Name → ExtractM Type
get-normalised-def  : Name → ExtractM Definition
\end{code}

The implementation of these operations is standard so we omit it here.

\begin{code}[hide]
monadExtractM .RawMonad.return x .runExtractM s = R.return (s , ok x)
monadExtractM .RawMonad._>>=_ m f .runExtractM s =
  runExtractM m s R.>>= λ where
    (s' , ok x)    → runExtractM (f x) s'
    (s' , error s) → R.return (s' , error s)

fail err .runExtractM s = R.return (s , error err)

infix 0 _update-err_

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
  base ← ExtractState.base <$> get-state
  liftTC (withReconstructed (dontReduceDefs base (R.normalise ty)))

get-normalised-def f =
  liftTC (withReconstructed (R.getDefinition f)) -- TODO: reintroduce normalisation of clauses
\end{code}


\subsection{The extractor}

The extractor itself consists of four functions that traverse the
different parts of the reflected Agda syntax and translate it to
PostScript commands:

\begin{code}
{-# TERMINATING #-}
extract-term     : Term → Pattern → ExtractM (List PsCmd)
extract-type     : Type → ExtractM ℕ
extract-clauses  : Clauses → ℕ → ExtractM (List PsCmd)
extract-def      : Name → ExtractM PsCmd
\end{code}

\begin{itemize}

\item \AF{extract-term} traverses an Agda term and translates it to a
list of PostScript commands. For example, it translates the expression
$\AF{add}\ (\AF{push}\ \AN{1}\ \AB{s})$ to $\AC{Push}\ \AN{1}\ \AC{∷}\
\AF{Add}\ \AC{∷}\ \AC{[]}$. It takes an additional argument of type
\AD{Pattern} in order to check that the stack used in the expression
(in this case \AB{s}) is identical to the input stack. Note that this
function has to be marked as termination due to the current
limitations of Agda's termination checker.

\item \AF{extract-type} traverses an Agda type and checks that it
takes one principal argument of type \AD{Stack} and returns a value of
type \AD{Stack}. In addition, it checks that all non-principal
arguments to the function are marked as runtime-irrelevant and can
thus safely be erased during extraction. If these checks succeed, it
returns the position of the principal argument.

\item \AF{extract-clauses} takes as input the clauses of a function
definition and the position of the principal argument (as computed by
\AF{extract-type}) and translates the clauses to a list of PostScript
commands. For example, consider the function \AF{non-zero}:
\begin{code}
non-zero : Stack ℕ (1 + n) → Stack ℕ (1 + n)
non-zero s@(_ # 0) = s
non-zero s@(_ # _) = s ▹ pop ▹ push 1
\end{code}
The clauses of \AF{non-zero} are translated to a conditional
expression in PostScript that checks whether the top element is zero:
\begin{lstlisting}[language=PostScript]
  0 index 0 eq { } { pop 1 } ifelse
\end{lstlisting}

\item Finally, \AF{extract-def} takes as input a (reflected) name of
an Agda function, gets its type and definition, and calls
\AF{extract-type} and \AF{extract-clauses} to translate it to a list
of PostScript commands.
\end{itemize}

In the remainder of this section, we explain the implementation of
these functions in more detail.

Working with reflected syntax in Agda can quickly become very verbose.
To reduce the syntactic noise, we make use of pattern synonyms for
commonly used pieces of syntax. As a convention, the names of these
pattern synonyms start with a backtick \` followed by the name of the
represented Agda construct. We give two representative examples, other
pattern synonyms are defined analogously.

\begin{code}
pattern `zero   = con (quote ℕ.zero) []
pattern `suc n  = con (quote ℕ.suc) (vArg n ∷ [])
\end{code}

\begin{code}[hide]
pattern vArg0 x = arg (arg-info visible (modality _ quantity-0)) x
pattern hArg0 x = arg (arg-info hidden (modality _ quantity-0)) x

pattern `Stack X n  = def (quote Stack) (vArg X ∷ vArg0 n ∷ [])
pattern _`#p_ x y   = con (quote Stack._#_) (_ ∷ vArg x ∷ vArg y ∷ [])
pattern _`#_ x y    = con (quote Stack._#_) (_ ∷ _ ∷ vArg x ∷ vArg y ∷ [])

pattern `push n s  = def (quote push) (_ ∷ _ ∷ vArg n ∷ vArg s ∷ [])
pattern `pop s     = def (quote pop) (_ ∷ _ ∷ vArg s ∷ [])
pattern `dup s     = def (quote dup) (_ ∷ _ ∷ vArg s ∷ [])
pattern `exch s    = def (quote exch) (_ ∷ _ ∷ vArg s ∷ [])
pattern `rot3 s    = def (quote rot3) (_ ∷ _ ∷ vArg s ∷ [])

pattern `add s  = def (quote add) (_ ∷ vArg s ∷ [])
pattern `sub s  = def (quote sub) (_ ∷ vArg s ∷ [])
pattern `mul s  = def (quote mul) (_ ∷ vArg s ∷ [])
pattern `eq s   = def (quote eq) (_ ∷ vArg s ∷ [])
pattern `gt s   = def (quote gt) (_ ∷ vArg s ∷ [])

pattern `index k s = def (quote index) (_ ∷ _ ∷ vArg k ∷ _ ∷ vArg s ∷ [])
pattern `subst-stack s = def (quote subst-stack) (_ ∷ _ ∷ _ ∷ _ ∷ vArg s ∷ [])
\end{code}

\begin{code}[hide]
stack-ok : Pattern → Term → ExtractM ⊤
\end{code}

\begin{AgdaAlign}
\begin{code}
extract-term v stackp = go v []
  where
  go : Term → List PsCmd → ExtractM (List PsCmd)
  go (`pop x)   acc = go x (Pop   ∷ acc)
  go (`dup x)   acc = go x (Dup   ∷ acc)
  go (`exch x)  acc = go x (Exch  ∷ acc)
  go (`rot3 x)  acc = go x (Rot3  ∷ acc)
  go (`add x)   acc = go x (Add   ∷ acc)
  go (`sub x)   acc = go x (Sub   ∷ acc)
  go (`mul x)   acc = go x (Mul   ∷ acc)
  go (`eq x)    acc = go x (Eq    ∷ acc)
  go (`gt x)    acc = go x (Ge    ∷ acc)
\end{code}

\begin{code}
  go (`push (lit (nat n)) x) acc =
    go x (Push n ∷ acc)
  go (`push k x) acc =
    fail ("extract-term: push with non-literal "
          <> showTerm k)
  go (`index (lit (nat n)) x) acc =
    go x (Index n ∷ acc)
  go (`index k x) acc =
    fail ("extract-term: index with non-literal "
          <> showTerm k)
\end{code}

\begin{code}
  go (`subst-stack x) acc = go x acc
\end{code}

\begin{code}
  go (def f args@(_ ∷ _)) acc = do
    mark-todo f
    ty  ← get-normalised-type f
    n   ← extract-type ty
      update-err ("trying to obtain type of `"
                 <> prettyName f <> "`: ")
    a   ← lookup-arg args n
    go a (FunCall (prettyName f) ∷ acc)
\end{code}

\begin{code}
  go v@(var x []) acc = do
    stack-ok stackp v
      update-err "extract-term var mismatch: "
    return acc
  go v@(_ `# _) acc = do
    stack-ok stackp v
      update-err "extract-term cons mismatch: "
    return acc
\end{code}


\begin{code}
  go t acc =
    fail ("failed with term `" <> showTerm t <> "`")
\end{code}


The function \AF{stack-ok} ensures that when we use
the stack, it corresponds to the stack that we got as the input to the
function.  So it ensures that we do not manipulate the stack in
arbitrary ways, but only through the primitive stack operations of
PostScript.


\begin{code}
stack-ok p@(p₁ `#p p₂) t@(t₁ `#  t₂) = do
  stack-ok p₁ t₁
  stack-ok p₂ t₂

stack-ok (var x) (var y []) =
  unless (does (x ℕ.≟ y))
    (fail "stack-ok: var/var mismatch")

stack-ok `zero `zero = return _

stack-ok (`suc x) (`suc y) = stack-ok x y
\end{code}


\begin{code}[hide]
stack-ok (lit (nat x)) (lit (nat y)) =
  unless (does (x ℕ.≟ y))
    (fail "stack-ok: lit/lit mismatch")

stack-ok x (lit (nat y)) = do
  x′ ← pattern-to-nat x
  unless (does (x′ ℕ.≟ y))
    (fail "stack-ok: nat/lit mismatch")
  where
    pattern-to-nat : Pattern → ExtractM ℕ
    pattern-to-nat `zero     = return 0
    pattern-to-nat (`suc x)  = suc <$> pattern-to-nat x
    pattern-to-nat _         = fail "not a suc/zero pattern"

stack-ok (lit (nat x)) y = do
  y′ ← term-to-nat y
  unless (does (x ℕ.≟ y′))
    (fail "stack-ok: lit/nat mismatch")
  where
    term-to-nat : Term → ExtractM ℕ
    term-to-nat `zero     = return 0
    term-to-nat (`suc x)  = suc <$> term-to-nat x
    term-to-nat _         = fail "stack-ok: not a suc/zero term"
\end{code}


\begin{code}
stack-ok p t = fail
  ("stack-ok: mismatch "
   <> showPattern p <> " and " <> showTerm t)
\end{code}



The function \AF{extract-type} defines what Agda types are valid
for functions in the embedding.  It also returns which argument
corresponds to the stack.

\begin{code}
extract-type x = go x false 0
  where
  go : Type → (st-arg : Bool) → (off : ℕ) → ExtractM ℕ
  go (Π[ s ∶ arg _ (`Stack X n) ] y) false o =
    go y true o
  go (Π[ s ∶ hArg0 _ ] y) b o =
    go y b (if b then o else 1 + o)
  go (`Stack X n) true o = return o
  go t _ _ =
    fail ("failed with type `" <> showTerm t <> "`")
\end{code}


When compiling the final clause, we skip compilation of the
pattern. This is a correct optimization because Agda enforces
completeness of definitions by pattern matching, so if the final case
is reached it is guaranteed to match.


\begin{code}
extract-clauses [] i =
  fail "extract-clauses: zero clauses found"
extract-clauses (absurd-clause _ _ ∷ ts) i =
  extract-clauses ts i
extract-clauses (clause _ ps t ∷ []) i = do
  stackp ← lookup-arg ps i
  extract-term t stackp
extract-clauses (clause _ ps t ∷ ts) i = do
  stackp  ← lookup-arg ps i
  ml      ← extract-stackp 0 stackp
  case ml of λ where
    nothing  → do
      extract-term t stackp
    (just l) → do
      t  ← extract-term t stackp
      ts ← extract-clauses ts i
      return (l ++ [ IfElse t ts ])
\end{code}

The implementation of \AF{extract-clauses} makes use of two
helper functions \AF{extract-stackp} and
\AF{extract-nap} to extract a boolean condition from a given
Agda pattern of type \AD{Stack} and \AD{ℕ}
respectively. They returns either \AC{just} the
condition as a list of PostScript commands, or
\AC{nothing} in case the pattern is guaranteed
to match and hence no conditional is needed.

\begin{code}
  where
  extract-stackp : (hd-idx : ℕ) → Pattern
                 → ExtractM (Maybe (List PsCmd))
  extract-natp : Pattern → ℕ
               → ExtractM (Maybe (List PsCmd))

  extract-stackp _      (var x)     = return nothing
  extract-stackp hd-idx (p₁ `#p p₂) =
    extract-natp p₂ 0 >>= λ where
      nothing   → extract-stackp (1 + hd-idx) p₁
      (just cmp) → do
        let l₁ = Index hd-idx ∷ cmp
        ml₂ ← extract-stackp (2 + hd-idx) p₁
        case ml₂ of λ where
          nothing   → return (just l₁)
          (just l₂) → return (just (l₁ ++ l₂ ++ [ And ]))
  extract-stackp _ _ =
    fail "extract-stackp: invalid stack pattern"

  extract-natp (var _)        0 = return nothing
  extract-natp (var _)        c = return (just (Push c ∷ Ge ∷ []))
  extract-natp `zero          c = return (just (Push c ∷ Eq ∷ []))
  extract-natp (`suc p)       c = extract-natp p (1 + c)
  extract-natp (lit (nat n))  c = return (just (Push (c + n) ∷ Eq ∷ []))
  extract-natp  _             _ =
    fail "extract-stackp: invalid nat pattern"
\end{code}


Finally, the function \AF{extract-def} extracts the function
with a given name, or fails on any other kind of Agda definition.

\begin{code}
extract-def f = do
  ty   ← get-normalised-type f
  deff ← get-normalised-def f
  case deff of λ where
    (function cs) → do
      i ← extract-type ty
      b ← extract-clauses cs i
      return (FunDef (prettyName f) b)
    _ → fail ("extract: attempting to extract `" <>
              prettyName f <> "` as function")
\end{code}



\subsection{Main extractor}

Explain very briefly that there is a common extraction part that we can (and do)
abstract away; and there is a language part that we are focusing on.


The function extract-defs traverses through the list of the functions
we need to extract and collects all the definitions.

Since any Agda development has a finite number of definitions and we
only process each definition once, this function is
terminating. However, the Agda termination checker does not detect
this, so we mark it as terminating manually using a pragma.

\begin{code}
{-# TERMINATING #-}
extract-defs : ExtractM (List PsCmd)
extract-defs = get-next-todo >>= λ where
  nothing  → return []
  (just f) → do
    x  ← extract-def f
    xs ← extract-defs
    return (x ∷ xs)
\end{code}

Main entry point of the extractor.

\begin{itemize}
\item \AB{base} is the set of base functions that we never traverse into.
\item \AB{n} is a starting function of the extraction
\end{itemize}

\begin{code}
macro
  extract : Name → Names → Term → TC ⊤
  extract n base hole =
    let initState = mkExtractState base [ n ] base in
    runExtractM extract-defs initState R.>>= λ where
      (_ , ok p)      → R.quoteTC (print-ps p) R.>>= R.unify hole
      (_ , error err) → R.typeError [ R.strErr err ]
\end{code}

We provide a default list of base functions that are ignored by the
extractor, but this list can be tailored to a specific program by
adding external library functions.

\begin{code}
base : List Name
base = quote add ∷ quote sub ∷ quote mul ∷ quote eq ∷ quote gt
     ∷ quote push ∷ quote pop ∷ quote dup ∷ quote exch
     ∷ quote rot3 ∷ quote index ∷ quote subst-stack ∷ []
\end{code}

Thanks to the theorem-proving capabilities of Agda, we can embed test
cases for the extractor as simple equality proofs. These test cases
are run automatically during type checking, so if a change to the
extractor causes one of them to fail it will not go unnoticed.

As a simple example, here is a test that \AF{add-1} is extracted
correctly:

\begin{code}

_ : lines (extract add-1 base) ≡
  ( "/add-1 {"
  ∷ "  1 add"
  ∷ "} def"
  ∷ [] )
_ = refl
\end{code}

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

dblsuc : Stack ℕ (1 + n) → Stack ℕ (2 + n)
dblsuc xs = add-1 (dup xs)

_ : lines (extract dblsuc base) ≡
  ( "/add-1 {"
  ∷ "  1 add"
  ∷ "} def"
  ∷ ""
  ∷ "/dblsuc {"
  ∷ "  dup add-1"
  ∷ "} def"
  ∷ [] )
_ = refl


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
\end{AgdaAlign}

\subsection{\label{sec:normalisation}Normalisation}
It is useful for inlining functions, and creating macros that can use arbitrary expressions
as long as their applications evaluate to postscript operators.
This is not essential and can be moved towards the end.

\subsection{\label{sec:controlling-reduction}Controlling Reduction}
This is essential, as we need to avoid inlining of the base operators, otherwsie
we won't be able to extact our pograms one-to-one.  Explain the mechanism.  Say that we have
added this to Agda?


\subsection{\label{sec:maptypes}Analysing Types}
Explain that all we need to do is to find the position of the stack argument, as well as
verify that the return type is also a stack argument.  In between we can have arbitrary
number of computationally irrelevant arguments.


\subsection{Pattern Matching}
The natural way to express functions in Agda is by means of pattern-matching, so it makes sense
to support it.  All we allow in patternmatching is to ``look'' at the stack argument and the
individual elements.  But we are not allowed to reshuffle the elements, we have to pass the
pattern exactly as it was matched (in some sense it is read-only pattern matching).

\subsection{\label{sec:translating-terms}Translating terms}
The core of the extraction is how do we translate terms.  Also this is the simplest part in
case of the PostScript example.

\subsection{Example}
Explain the entire extaction process for the given example?

Shall we talk about termination and how do we deal with that?


\subsection{\label{sec:rewriting}Rewriting}
We can mention that rewriting is super useful feature that can be used as an optimisation
prior to extraction.
