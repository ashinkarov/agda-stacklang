
\begin{code}[hide]
open import Category.Monad

open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Fin as F using (Fin; zero; suc; fromℕ<)
open import Data.List as L using (List; []; _∷_; _++_; [_]; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_) renaming (_∸_ to _-_)
open import Data.Nat.Properties
open import Data.Nat.Show using () renaming (show to showNat)
open import Data.Product
open import Data.String as S using (String; _≈?_)
open import Data.Unit
open import Data.Vec as V using (Vec; []; _∷_)

open import Function using (case_of_; flip)

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
unlines = intercalate "\n\n"

\end{code}


\section{Extraction}

In this section, we show a concrete example of an extractor
implemented using reflection in Agda. On a basic level, the extractor
is a simple traversal of the syntax that maps basic stack operations
such as \AgdaFunction{dup} and \AgdaFunction{add} to their
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
the same as the input stack. See the description of
\AgdaFunction{extract-term} below for more details.

\item Operations on stacks can take arguments besides the `main' stack
argument, as long as these other arguments are computationally
irrelevant. The extractor thus needs to determine which argument of a
given function corresponds to the input stack, and that the other
arguments can indeed be erased. See the description of
\AgdaFunction{extract-type} for more details.

\item We allow functions on stacks to to make limited use of pattern
matching on values on the stack, as for example in the definition of
\AgdaFunction{rep}. The extractor needs to translate these patterns to
conditional statements. See the description of
\AgdaFunction{extract-pattern} and \AgdaFunction{extract-clauses}
below for more details.

\end{itemize}


\subsection{Target syntax}

In the end, the extractor outputs the PostScript syntax as a plain
string. However, it is useful to work with a basic abstract syntax
representation as an intermediate stage:

\begin{code}
data PsCmd : Set where
  Pop Dup Exch Add Sub Mul Eq Ge And : PsCmd
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

print-ps es = intercalate "\n\n" (reverse (L.map (expr-to-string 0) es))
\end{code}


\subsection{The extractor}

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

fail         : String → ExtractM X
_updateErr_  : ExtractM X → String → ExtractM X
getNextTodo  : ExtractM (Maybe Name)
isDone       : Name → ExtractM Bool
markAsTodo   : Name → ExtractM ⊤
markAsDone   : Name → ExtractM ⊤
\end{code}

The monad also provides two operations for getting normalized types
and definitions of a given symbol. This can be used for example for
inlining Agda functions that cannot be translated to PostScript, or
for applying domain-specific optimizations through the use of rewrite
rules.

\begin{code}
get-normalised-type : Name → ExtractM Type
get-normalised-def  : Name → ExtractM Definition
\end{code}

\begin{code}[hide]
monadExtractM .RawMonad.return x .runExtractM s = R.return (s , ok x)
monadExtractM .RawMonad._>>=_ m f .runExtractM s =
  runExtractM m s R.>>= λ where
    (s' , ok x)    → runExtractM (f x) s'
    (s' , error s) → R.return (s' , error s)

fail err .runExtractM s = R.return (s , error err)

infix 0 _updateErr_

(m updateErr err1) .runExtractM s = m .runExtractM s R.>>= λ where
  (s' , ok x)      → R.return (s' , ok x)
  (s' , error err2) → R.return (s' , error (err1 <> "\n" <> err2))

getExtractState : ExtractM ExtractState
getExtractState .runExtractM s = R.return (s , ok s)

modifyExtractState : (ExtractState → ExtractState) → ExtractM ⊤
modifyExtractState f .runExtractM s = R.return (f s , ok _)

setExtractState : ExtractState → ExtractM ⊤
setExtractState s = modifyExtractState (λ _ → s)

isDone f = do
  done ← ExtractState.done <$> getExtractState
  return (elem (f RN.≟_) done)

markAsTodo f = modifyExtractState λ st → record st { todo = ExtractState.todo st ++ [ f ] }

markAsDone f = modifyExtractState λ st → record st { done = f ∷ ExtractState.done st }

getNextTodo = do
  todo ← ExtractState.todo <$> getExtractState
  go todo
  where
    go : List Name → ExtractM (Maybe Name)
    go [] = return nothing
    go (f ∷ fs) = do
      modifyExtractState λ st → record st { todo = fs }
      done ← isDone f
      if done then
          go fs
        else do
          markAsDone f
          return (just f)

liftTC       : TC X → ExtractM X
liftTC m .runExtractM s = m R.>>= λ x → R.return (s , ok x)

get-normalised-type f = do
  ty   ← liftTC (R.getType f)
  base ← ExtractState.base <$> getExtractState
  liftTC (withReconstructed (dontReduceDefs base (R.normalise ty)))

get-normalised-def f =
  liftTC (withReconstructed (R.getDefinition f)) -- TODO: reintroduce normalisation of clauses
\end{code}

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

pattern `add s  = def (quote add) (_ ∷ vArg s ∷ [])
pattern `sub s  = def (quote sub) (_ ∷ vArg s ∷ [])
pattern `mul s  = def (quote mul) (_ ∷ vArg s ∷ [])
pattern `eq s   = def (quote eq) (_ ∷ vArg s ∷ [])
pattern `gt s   = def (quote gt) (_ ∷ vArg s ∷ [])

pattern `index k s = def (quote index) (_ ∷ _ ∷ vArg k ∷ _ ∷ vArg s ∷ [])
pattern `subst-stack s = def (quote subst-stack) (_ ∷ _ ∷ _ ∷ _ ∷ vArg s ∷ [])
\end{code}


\begin{code}
extract-def      : Name → ExtractM PsCmd
extract-type     : Type → ExtractM ℕ
extract-clauses  : Clauses → ℕ → ExtractM (List PsCmd)

{-# TERMINATING #-}
extract-term     : Term → Pattern → ExtractM (List PsCmd)
\end{code}

This function ensure that when we use the stack, it corresponds to
the stack that we got as the input to the function.
So it ensures that we do not manipulate the stack in arbitrary ways,
but only through the primitive stack operations of postscript.

\begin{code}
pattern-match-ok : Pattern → Term → ExtractM ⊤
\end{code}
\begin{code}[hide]
pattern-match-ok p@(p₁ `#p p₂) t@(t₁ `#  t₂) = do
  pattern-match-ok p₁ t₁
  pattern-match-ok p₂ t₂

pattern-match-ok (var x) (var y []) with x ℕ.≟ y
... | yes _ = return _
... | no  _ = fail "pattern-match-ok: variables do not match"

pattern-match-ok (lit (nat x)) (lit (nat y)) with x ℕ.≟ y
... | yes _ = return _
... | no  _ = fail "pattern-match-ok: literal vaues do not match"

pattern-match-ok `zero `zero = return _

pattern-match-ok (`suc x) (`suc y) = pattern-match-ok x y

pattern-match-ok (lit (nat x)) y = do
  y′ ← extract-nat y
  case x ℕ.≟ y′ of λ where
    (yes _) → return _
    (no  _) → fail "pattern-match-ok: invalid literal/number match"
  where
    extract-nat : Term → ExtractM ℕ
    extract-nat `zero = return 0
    extract-nat (`suc x) = suc <$> extract-nat x
    extract-nat _ = fail "not a suc/zero term"

pattern-match-ok x (lit (nat y)) = do
  x′ ← extract-pattern-nat x
  case x′ ℕ.≟ y of λ where
    (yes _) → return _
    (no  _) → fail "pattern-match-ok: invalid literal/number match"
  where
    extract-pattern-nat : Pattern → ExtractM ℕ
    extract-pattern-nat `zero = return 0
    extract-pattern-nat (`suc x) = suc <$> extract-pattern-nat x
    extract-pattern-nat _ = fail "not a suc/zero pattern"

pattern-match-ok p t = fail
  ("pattern-match-ok: invalid stack variable pattern: "
   <> showPattern p <> " and " <> showTerm t)
\end{code}


\begin{code}
extract-term v@(var x []) p = do
  pattern-match-ok p v
    updateErr "extract-term var mismatch: "
  return []
extract-term v@(_ `# _) p = do
  pattern-match-ok p v
    updateErr "extract-term cons mismatch: "
  return []
\end{code}

\begin{code}
extract-term (`push (lit (nat n)) x) p =
  Push n ∷_ <$> extract-term x p
extract-term (`push k x) p =
  fail ("extract-term: push with non-literal "
        <> showTerm k)
\end{code}

\begin{code}
extract-term (`pop x)   p = Pop   ∷_ <$> extract-term x p
extract-term (`dup x)   p = Dup   ∷_ <$> extract-term x p
extract-term (`exch x)  p = Exch  ∷_ <$> extract-term x p
extract-term (`add x)   p = Add   ∷_ <$> extract-term x p
extract-term (`sub x)   p = Sub   ∷_ <$> extract-term x p
extract-term (`mul x)   p = Mul   ∷_ <$> extract-term x p
extract-term (`eq x)    p = Eq    ∷_ <$> extract-term x p
extract-term (`gt x)    p = Ge    ∷_ <$> extract-term x p
\end{code}

\begin{code}
extract-term (`index (lit (nat n)) x) p =
  Index n ∷_ <$> extract-term x p
extract-term (`index k x) p =
  fail ("extract-term: index with non-literal "
        <> showTerm k)
\end{code}

\begin{code}
extract-term (`subst-stack x) p = extract-term x p
\end{code}

\begin{code}
extract-term (def f args@(_ ∷ _)) p = do
  ty ← get-normalised-type f
  markAsTodo f
  n ← extract-type ty
    updateErr ("trying to obtain type of `"
               <> showName f <> "`: ")
  arg i a ← index-args args n
  b ← extract-term a p
  return (FunCall (showName f) ∷ b)
  where
    index-args : List (Arg Term) → ℕ → ExtractM (Arg Term)
    index-args []       _        = fail "index out of range"
    index-args (a ∷ as) 0        = return a
    index-args (a ∷ as) (suc i)  = index-args as i
\end{code}

\begin{code}
extract-term t _ =
  fail ("failed with term `" <> showTerm t <> "`")
\end{code}




The function \AgdaFunction{extract-type} defines what Agda types are valid
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
      fail ("failed with type `"
            <> showTerm t <> "`")
\end{code}

\begin{code}[hide]
lookup-pattern : List (Arg Pattern) → ℕ → ExtractM Pattern
lookup-pattern ((arg _ x) ∷ xs) zero = return x
lookup-pattern (_ ∷ xs) (suc n) = lookup-pattern xs n
lookup-pattern _ _ = fail "extract-clauses: invalid stack variable index in patterns"
\end{code}

The function \AgdaFunction{extract-pattern} extracts a boolean
condition from a given Agda pattern consisting of the constructors
\AgdaInductiveConstructor{zero}, \AgdaInductiveConstructor{suc}, and
pattern variables. It returns either \AgdaInductiveConstructor{just}
the condition as a list of PostScript commands, or
\AgdaInductiveConstructor{nothing} in case the pattern is guaranteed
to match and hence no conditional is needed.

\begin{code}
extract-pattern : (hd-idx : ℕ) → Pattern
                → ExtractM (Maybe (List PsCmd))
extract-pattern _      (var x)     = return nothing
extract-pattern hd-idx (p₁ `#p p₂) =
  match-cond p₂ 0 >>= λ where
    nothing   → extract-pattern (1 + hd-idx) p₁
    (just (cmp , c)) → do
      let l₁ = Index hd-idx ∷ Push c ∷ cmp ∷ []
      ml₂ ← extract-pattern (2 + hd-idx) p₁
      case ml₂ of λ where
        nothing   → return (just l₁)
        (just l₂) → return (just (l₁ ++ l₂ ++ [ And ]))
  where
    match-cond : Pattern → ℕ
               → ExtractM (Maybe (PsCmd × ℕ))
    match-cond (var _)        0 = return nothing
    match-cond (var _)        c = return (just (Ge , c))
    match-cond `zero          c = return (just (Eq , c))
    match-cond (`suc p)       c = match-cond p (1 + c)
    match-cond (lit (nat n))  c = return (just (Eq , c + n))
    match-cond  _             _   =
      fail "extract-pattern: invalid nat pattern"
extract-pattern _ _ =
  fail "extract-pattern: invalid stack pattern"
\end{code}


Note: when compiling the final clause, we skip compilation of the
pattern. This is a correct optimization because Agda enforces
completeness of definitions by pattern matching, so if the final case
is reached it is guaranteed to match.

\begin{code}
extract-clauses [] i =
  fail "extract-clauses: zero clauses found"
extract-clauses (clause _ ps t ∷ []) i = do
  p ← lookup-pattern ps i
  t ← extract-term t p
  return (L.reverse t)

extract-clauses (clause _ ps t ∷ ts) i = do
  stackp  ← lookup-pattern ps i
  ml      ← extract-pattern 0 stackp
  case ml of λ where
    nothing  → do
      t ← extract-term t stackp
      return (L.reverse t)
    (just l) → do
      t  ← extract-term t stackp
      ts ← extract-clauses ts i
      return (l ++ [ IfElse (L.reverse t) ts ])

extract-clauses (absurd-clause _ _ ∷ ts) i =
  extract-clauses ts i
\end{code}

Finally, the function \AgdaFunction{extract-def} extracts the function
with a given name, or fails on any other kind of Agda definition.

\begin{code}
extract-def f = do
  ty   ← get-normalised-type f
  deff ← get-normalised-def f
  case deff of λ where
    (function cs) → do
      t ← extract-type ty
      b ← extract-clauses cs t
      return (FunDef (showName f) b)
    _ → fail ("extract: attempting to extract `" <>
              showName f <> "` as function")
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
extract-defs = getNextTodo >>= λ where
  nothing  → return []
  (just f) → do
    x  ← extract-def f
    xs ← extract-defs
    return (x ∷ xs)
\end{code}

Main entry point of the extractor.

\begin{itemize}
\item \AgdaBound{base} is the set of base functions that we never traverse into.
\item \AgdaBound{n} is a starting function of the extraction
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

\begin{code}[hide]
base : List Name
base = quote add ∷ quote sub ∷ quote dup ∷ quote push ∷ quote pop
     ∷ quote index ∷ quote subst-stack ∷ quote exch {-∷ quote rot3-}
     {-∷ quote iframep-} ∷ []

extract-add-1 = extract add-1 base

_ : extract-add-1 ≡ "/psembedding.add-1 {\n  1 add\n} def\n"
_ = refl

dblsuc : Stack ℕ (1 + n) → Stack ℕ (2 + n)
dblsuc xs = add-1 (dup xs)

extract-dblsuc = extract dblsuc base

_ : extract-dblsuc ≡ "/psembedding.add-1 {\n  1 add\n} def\n\n\n/extraction.dblsuc {\n  dup psembedding.add-1\n} def\n"
_ = refl


extract-sqsum = extract sqsum base

_ : extract-sqsum ≡ "/psembedding.sqsum {\n  dup mul exch dup mul exch add\n} def\n"
_ = refl

extract-rep-simple =  extract RepSimple.rep base

_ : extract-rep-simple ≡
  "/psembedding.RepSimple.rep {\n  0 index 0 eq \n  {\n    pop pop\n  }\n  {\n    1 sub 1 index exch psembedding.RepSimple.rep\n  } ifelse\n\n} def\n"
_ = refl

\end{code}

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
