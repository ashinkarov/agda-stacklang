
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

open import Reflection as R hiding (return; _>>=_; _>>_)
open import Reflection.Term
import      Reflection.Name as RN
open import Agda.Builtin.Reflection using (withReconstructed; dontReduceDefs; onlyReduceDefs)

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

intercalate : (delim : String) → List String → String
intercalate d [] = ""
intercalate d (x ∷ []) = x
intercalate d (x ∷ xs) = x S.++ d S.++ intercalate d xs
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
\AgdaFunction{extract-type} and \AgdaFunction{extract-function-type}
for more details.

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
  Pop Dup Exch Add Sub Mul Eq Ge And
           : PsCmd
  Push     : ℕ → PsCmd
  If       : List PsCmd → PsCmd
  IfElse   : List PsCmd → List PsCmd → PsCmd
  FunDef   : String → List PsCmd → PsCmd
  Index    : ℕ → PsCmd
  FunCall  : String → PsCmd
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
                           S.++ indent ind S.++ "{\n"
                           S.++ indent ind S.++ intercalate " " (lexpr-to-string (1 + ind) xs) S.++ "\n"
                           S.++ indent ind S.++ "\n} if\n"
expr-to-string ind (FunDef n xs) = indent ind S.++ "/" S.++ n S.++ " {\n"
                                S.++ indent (1 + ind) S.++ intercalate " " (lexpr-to-string (1 + ind) xs) S.++ "\n"
                                S.++ indent ind S.++ "} def\n"
expr-to-string ind (Index x) = showNat x S.++ " index"
expr-to-string ind (FunCall x) = x
expr-to-string ind (IfElse xs ys) = "\n"
                                 S.++ indent ind S.++ "{\n"
                                 S.++ indent (1 + ind) S.++ intercalate " " (lexpr-to-string (1 + ind) xs) S.++ "\n"
                                 S.++ indent ind S.++ "}\n"
                                 S.++ indent ind S.++ "{\n"
                                 S.++ indent (1 + ind) S.++ intercalate " " (lexpr-to-string (1 + ind) ys) S.++ "\n"
                                 S.++ indent ind S.++ "} ifelse\n"

lexpr-to-string ind [] = []
lexpr-to-string ind (x ∷ xs) = expr-to-string ind x ∷ lexpr-to-string ind xs
\end{code}


\subsection{The extractor}

\begin{code}[hide]
Prog = String

emptyProg : Prog
emptyProg = ""

-- This is a `Maybe`-like data type except that nothing
-- is extended with a string argument, to carry around the error.
data Err {a} (A : Set a) : Set a where
  error : String → Err A
  ok    : A → Err A

-- The state used at the top-most and term-level extraction.
record ExtractState : Set where
  constructor mkExtractState
  field
    funs : Names   -- Functions to extract
    base : Names   -- Atomic functions that we do not traverse into.
    done : Names   -- Functions that we have processed.
    defs : Prog    -- Definitions such as lifted functions, function declarations, etc.
    cnt  : ℕ       -- Source of fresh variables
\end{code}

\begin{code}
record ExtractM (X : Set) : Set where
  field
    runExtractM : ExtractState → TC (ExtractState × Err X)
\end{code}

\begin{code}[hide]
open ExtractM

monadExtractM : RawMonad ExtractM
monadExtractM .RawMonad.return x .runExtractM s = R.return (s , ok x)
monadExtractM .RawMonad._>>=_ m f .runExtractM s =
  bindTC (runExtractM m s) λ where
    (s' , ok x)    → runExtractM (f x) s'
    (s' , error s) → R.return (s' , error s)

open RawMonad monadExtractM
\end{code}

\begin{code}
fail : String → ExtractM X

_updateErr_ : ExtractM X → (String → String) → ExtractM X

liftTC : TC X → ExtractM X

markAsDone : Name → ExtractM ⊤
\end{code}

\begin{code}[hide]
fail err .runExtractM s = R.return (s , error err)

infix 0 _updateErr_

(m updateErr f) .runExtractM s = m .runExtractM s R.>>= λ where
  (s' , ok x)      → R.return (s' , ok x)
  (s' , error err) → R.return (s' , error (f err))

liftTC m .runExtractM s = m R.>>= λ x → R.return (s , ok x)

getExtractState : ExtractM ExtractState
getExtractState .runExtractM s = R.return (s , ok s)

modifyExtractState : (ExtractState → ExtractState) → ExtractM ⊤
modifyExtractState f .runExtractM s = R.return (f s , ok _)

setExtractState : ExtractState → ExtractM ⊤
setExtractState s = modifyExtractState (λ _ → s)

markAsDone fname = modifyExtractState λ k → record k { funs = ExtractState.funs k ++ [ fname ] }
\end{code}

\begin{code}
pattern vArg0 x = arg (arg-info visible (modality _ quantity-0)) x
pattern hArg0 x = arg (arg-info hidden (modality _ quantity-0)) x

pattern `ℕ = def (quote ℕ) []
pattern `zero = con (quote ℕ.zero) []
pattern `suc n = con (quote ℕ.suc) (vArg n ∷ [])
pattern `Stack X n = def (quote Stack) (vArg X ∷ vArg0 n ∷ [])
pattern _`#p_ x y = con (quote Stack._#_) (_ ∷ vArg x ∷ vArg y ∷ [])
pattern _`#_ x y = con (quote Stack._#_) (_ ∷ _ ∷ vArg x ∷ vArg y ∷ [])

pattern `push n s  = def (quote push) (_ ∷ _ ∷ vArg n ∷ vArg s ∷ [])
pattern `pop s  = def (quote pop) (_ ∷ _ ∷ vArg s ∷ [])
pattern `dup s  = def (quote dup) (_ ∷ _ ∷ vArg s ∷ [])
pattern `exch s = def (quote exch) (_ ∷ _ ∷ vArg s ∷ [])

pattern `add s  = def (quote add) (_ ∷ vArg s ∷ [])
pattern `sub s  = def (quote sub) (_ ∷ vArg s ∷ [])
pattern `mul s  = def (quote mul) (_ ∷ vArg s ∷ [])
pattern `eq s  = def (quote eq) (_ ∷ vArg s ∷ [])
pattern `gt s  = def (quote gt) (_ ∷ vArg s ∷ [])

pattern `index k s = def (quote index) (_ ∷ _ ∷ vArg k ∷ _ ∷ vArg s ∷ [])
pattern `subst-stack s = def (quote subst-stack) (_ ∷ _ ∷ _ ∷ _ ∷ vArg s ∷ [])
\end{code}

This function ensure that when we use the stack, it corresponds to
the stack that we got as the input to the function.
So it ensures that we do not manipulate the stack in arbitrary ways,
but only through the primitive stack operations of postscript.

\begin{code}
pat-match-term : Pattern → Term → ExtractM ⊤
\end{code}
\begin{code}[hide]
pat-match-term p@(p₁ `#p p₂)
               t@(t₁ `#  t₂) = do
  pat-match-term p₁ t₁
  pat-match-term p₂ t₂

pat-match-term (var x) (var y []) with x ℕ.≟ y
... | yes _ = return _
... | no  _ = fail "pat-match-term: variables do not match"

pat-match-term (lit (nat x)) (lit (nat y)) with x ℕ.≟ y
... | yes _ = return _
... | no  _ = fail "pat-match-term: literal vaues do not match"

pat-match-term `zero `zero = return _

pat-match-term (`suc x) (`suc y) = pat-match-term x y

pat-match-term (lit (nat x)) y = do
  y′ ← extract-nat y
  case x ℕ.≟ y′ of λ where
    (yes _) → return _
    (no  _) → fail "pat-match-term: invalid literal/number match"
  where
    extract-nat : Term → ExtractM ℕ
    extract-nat `zero = return 0
    extract-nat (`suc x) = suc <$> extract-nat x
    extract-nat _ = fail "not a suc/zero term"

pat-match-term x (lit (nat y)) = do
  x′ ← extract-pattern-nat x
  case x′ ℕ.≟ y of λ where
    (yes _) → return _
    (no  _) → fail "pat-match-term: invalid literal/number match"
  where
    extract-pattern-nat : Pattern → ExtractM ℕ
    extract-pattern-nat `zero = return 0
    extract-pattern-nat (`suc x) = suc <$> extract-pattern-nat x
    extract-pattern-nat _ = fail "not a suc/zero pattern"

pat-match-term p t = fail
  ("pat-match-term: invalid stack variable pattern: "
   S.++ showPattern p S.++ " and " S.++ showTerm t)
\end{code}

\begin{code}
extract-function      : Type → List Clause → Name → ExtractM PsCmd
extract-function-type : Type → ExtractM ℕ
extract-clauses       : Clauses → ℕ → ExtractM (List PsCmd)

{-# TERMINATING #-}
extract-term          : Term → (stack-arg-pat : Pattern) → ExtractM (List PsCmd)
\end{code}


\begin{code}
extract-term v@(var x []) p = do
  pat-match-term p v
    updateErr ("variable does not match arg pattern: " S.++_)
  return []

extract-term v@(_ `# _) p = do
  pat-match-term p v
    updateErr ("stack constructor does not match arg pattern: " S.++_)
  return []

extract-term (`push (lit (nat n)) x) p =
  Push n ∷_ <$> extract-term x p

extract-term (`pop x) p =
  Pop ∷_ <$> extract-term x p

extract-term (`dup x) p =
  Dup ∷_ <$> extract-term x p

extract-term (`exch x) p =
  Exch ∷_ <$> extract-term x p

extract-term (`add x) p =
  Add ∷_ <$>  extract-term x p

extract-term (`sub x) p =
  Sub ∷_ <$> extract-term x p

extract-term (`mul x) p =
  Mul ∷_ <$>  extract-term x p

extract-term (`eq x) p =
  Eq ∷_ <$> extract-term x p

extract-term (`gt x) p =
  Ge ∷_ <$>  extract-term x p

extract-term (`index (lit (nat n)) x) p =
  Index n ∷_ <$> extract-term x p

extract-term (`subst-stack x) p =
  extract-term x p
\end{code}

\begin{code}[hide]
extract-term (`index k x) p = do
  fail ("extract-term: index with non-literal " S.++ showTerm k)

extract-term (`push k x) p =
  fail ("extract-term: push with non-literal " S.++ showTerm k)
\end{code}

\begin{code}
extract-term (def fname args@(_ ∷ _)) p = do
  ty ← liftTC (getType fname)
  markAsDone fname
  n ← extract-function-type ty
    updateErr (("trying to obtain type of `" S.++ showName fname S.++ "` with: ") S.++_)
  arg i a ← index-args args n
  b ← extract-term a p
  return (FunCall (showName fname) ∷ b)
  where
    index-args : List (Arg Term) → ℕ → ExtractM (Arg Term)
    index-args []       _       = fail "index out of range"
    index-args (a ∷ as) 0       = return a
    index-args (a ∷ as) (suc i) = index-args as i

extract-term t _ = fail ("failed with the term `" S.++ showTerm t S.++ "`")
\end{code}




\begin{code}
extract-function ty [] n =
  fail "extract-function: got zero clauses in a function definition"

extract-function ty cs fname = do
  t ← extract-function-type ty
  b ← extract-clauses cs t
  return (FunDef (showName fname) b)
\end{code}


The function \AgdaFunction{extract-type} defines what Agda types are valid
for functions in the embedding.  It also returns which argument
corresponds to the stack.

\begin{code}
extract-function-type x = extract-type x false 0
  where
    extract-type : Type → (st-arg : Bool) → (off : ℕ) → ExtractM ℕ
    extract-type (Π[ s ∶ arg _ (`Stack X n) ] y) false o =
      extract-type y true o
    extract-type (Π[ s ∶ hArg0 _ ] y) false o =
      extract-type y false (1 + o)
    extract-type (Π[ s ∶ hArg0 _ ] y) true o =
      extract-type y true o
    extract-type (`Stack X n) true o = return o
    extract-type t _ _ =
      fail ("failed with the type `" S.++ showTerm t S.++ "`")
\end{code}

\begin{code}[hide]
lookup-pattern : List (Arg Pattern) → ℕ → ExtractM Pattern
lookup-pattern ((arg _ x) ∷ xs) zero = return x
lookup-pattern (_ ∷ xs) (suc n) = lookup-pattern xs n
lookup-pattern _ _ = fail "extract-clauses: invalid stack variable index in patterns"
\end{code}

The function \AgdaFunction{extract-pattern} extracts a boolean
condition from a given Agda pattern consisting of the constructors
\AgdaInductiveConstructor{zero}, \AgdaInductiveConstructor{suc}, and pattern variables. It returns the
condition as a list of PostScript commands together with the

\begin{code}
extract-pattern : (hd-idx : ℕ) → Pattern → ExtractM (Maybe (List PsCmd))
extract-pattern hd-idx (p₁ `#p p₂) = do
  ml₁ ← extract-nat-pattern p₂ hd-idx 0
  case ml₁ of λ where
    nothing   → extract-pattern (1 + hd-idx) p₁
    (just l₁) → do
      ml₂ ← extract-pattern (2 + hd-idx) p₁
      case ml₂ of λ where
        nothing   → return (just l₁)
        (just l₂) → return (just (l₁ ++ l₂ ++ [ And ]))
 where
    extract-nat-pattern : Pattern → (hd-idx suc-count : ℕ) → ExtractM (Maybe (List PsCmd))
    extract-nat-pattern (var _)        _       0   =
      return nothing
    extract-nat-pattern (var _)        hd-idx  c   =
      return (just (Index hd-idx ∷ Push c ∷ Ge ∷ []))
    extract-nat-pattern (lit (nat n))  hd-idx  c   =
      return (just (Index hd-idx ∷ Push (c + n) ∷ Eq ∷ []))
    extract-nat-pattern (`suc x)       hd-idx  c   =
      extract-nat-pattern x hd-idx (1 + c)
    extract-nat-pattern `zero          hd-idx  c   =
      return (just (Index hd-idx ∷ Push c ∷ Eq ∷ []))
    extract-nat-pattern _              _       _   =
      fail "extract-nat-pattern: Invalid pattern for ℕ argument"

extract-pattern _ (var x) = return nothing
extract-pattern _ _ = fail "extract-pattern: invalid stack pattern _#_ expected"
\end{code}


Note: when compiling the final clause, we skip compilation of the
pattern. This is a correct optimization because Agda enforces
completeness of definitions by pattern matching, so if the final case
is reached it is guaranteed to match.

\begin{code}
extract-clauses [] num-arg = fail "extract-clauses: zero clauses found"
extract-clauses (clause _ ps t ∷ []) num-arg = do
  p ← lookup-pattern ps num-arg
  t ← extract-term t p
  return (L.reverse t)

extract-clauses (clause _ ps t ∷ ts) num-arg = do
  argp ← lookup-pattern ps num-arg
  ml   ← extract-pattern 0 argp
  case ml of λ where
    nothing  → do
      t ← extract-term t argp
      return (L.reverse t)
    (just l) → do
      t  ← extract-term t argp
      ts ← extract-clauses ts num-arg
      return (l ++ [ IfElse (L.reverse t) ts ])


extract-clauses (absurd-clause _ _ ∷ ts) num-arg =
  extract-clauses ts num-arg

\end{code}




\subsection{Main extractor}

Explain very briefly that there is a common extraction part that we can (and do)
abstract away; and there is a language part that we are focusing on.

\begin{code}[hide]
extract-funp : Type → List Clause → Name → ExtractM Prog
extract-funp ty te n = do
  e ← extract-function ty te n
  return (expr-to-string 0 e)

{-# TERMINATING #-}
extract-fold : ExtractM String
-- Traverse through the list of the functions we need to extract
-- and collect all the definitions.
extract-fold = do
    s@(mkExtractState fs ba done _ c) ← getExtractState
    case fs of λ where
      []       → return ""
      (f ∷ fs) → case elem (f RN.≟_) done of λ where
        true → do
          modifyExtractState λ k → record k{ funs = fs }
          extract-fold
        false → do
          ty ← liftTC (getType f)
          ty ← liftTC (withReconstructed (dontReduceDefs ba (normalise ty)))
          deff ← liftTC (withReconstructed (getDefinition f))
          case deff of λ where
            (function cs) → do

                -- cs ← norm-clauses cs ba
                setExtractState (mkExtractState fs ba (f ∷ done) emptyProg c)
                -- Extract the function and make an error more specific in
                -- case extraction fails.
                --(ok q) ← lift-mstate {RM = monadTC} $ extract-fun ty te f
                --  where (error x) → return (error ("in function " S.++ showName f S.++ ": " S.++ x))
                q ← extract-funp ty cs f
                defs ← ExtractState.defs <$> getExtractState
                let q = defs S.++ q
                   --R.modify $! λ k → record k{ defs = ε }
                kst ← getExtractState
                  --let q = ExtractState.defs kst ⊕ q
                setExtractState (record kst{ defs = emptyProg })
                -- Do the rest of the functions
                p ← extract-fold
                return (p S.++ "\n\n" S.++ q)
            _ →
              fail ("extract: attempting to extract `" S.++ showName f S.++ "` as function")
\end{code}

Main entry point of the extractor.
\begin{itemize}
\item \AgdaBound{n} is a starting function of the extraction
\item \AgdaBound{base} is the set of base functions that we never traverse into.
\item \AgdaBound{skip} is the list of functions that we have traversed already.
\end{itemize}

The difference between the two is that \AgdaBound{base} would be
passed to \AgdaFunction{dontReduceDefs}, hence never inlined; whereas
\AgdaBound{skip} mainly avoids potential recursive extraction.


\begin{code}
macro
  extract : Name → Names → Names → Term → TC ⊤
  extract n base skip hole =
    runExtractM extract-fold (mkExtractState [ n ] base skip emptyProg 1) R.>>= λ where
      (_ , ok p)      → quoteTC p R.>>= unify hole
      (_ , error err) → typeError [ strErr err ]
\end{code}

\begin{code}[hide]
base : List Name
base = quote add ∷ quote sub ∷ quote dup ∷ quote push ∷ quote pop
     ∷ quote index ∷ quote subst-stack ∷ quote exch {-∷ quote rot3-}
     {-∷ quote iframep-} ∷ []

extract-stack-id = extract stack-id base base

_ : extract-stack-id ≡ "\n\n/psembedding.stack-id {\n  \n} def\n"
_ = refl

extract-dblsuc = extract dblsuc base base

_ : extract-dblsuc ≡ "\n\n/psembedding.add1 {\n  1 add\n} def\n\n\n/psembedding.dblsuc {\n  dup psembedding.add1\n} def\n"
_ = refl


extract-sqsum = extract sqsum base base

_ : extract-sqsum ≡ "\n\n/psembedding.sqsum {\n  dup mul exch dup mul add\n} def\n"
_ = refl

extract-rep-simple =  extract RepSimple.rep base base

_ : extract-rep-simple ≡
  "\n\n/psembedding.RepSimple.rep {\n  0 index 0 eq \n  {\n    pop pop\n  }\n  {\n    1 sub 1 index exch psembedding.RepSimple.rep\n  } ifelse\n\n} def\n"
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
