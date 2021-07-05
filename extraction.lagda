
\begin{code}[hide]
open import Category.Monad

open import Function using (case_of_; flip)

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

open import Level using (Level) renaming (zero to lzero; suc to lsuc)

open import Reflection as R hiding (return; _>>=_; _>>_)
open import Reflection.Term
import      Reflection.Name as RN
open import Agda.Builtin.Reflection using (withReconstructed; dontReduceDefs; onlyReduceDefs)

open import Relation.Nullary
open import Relation.Unary
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


\subsection{Shallow embedding of PostScript in Agda}

We start by providing a \emph{shallow} embedding of PostScript in
Agda. Since PostScript is a stack-based language, the first step is to
represent the stack in Agda.

\begin{code}
data Stack (X : Set) : @0 ℕ → Set where
  []  : Stack X 0
  _#_ : Stack X n → X → Stack X (suc n)

hd : ∀ {X n} → Stack X (1 + n) → X
hd (_ # x) = x

tl : ∀ {X n} → Stack X (1 + n) → Stack X n
tl (xs # _) = xs
\end{code}

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
\end{code}

\begin{code}
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






\subsection{Target syntax}



\begin{code}
data PsCmd : Set where
  Push : ℕ → PsCmd
  Dup Add Mul Eq Ge And Pop Sub Exch Rot3 : PsCmd
  If : List PsCmd → PsCmd
  IfElse : List PsCmd → List PsCmd → PsCmd
  FunDef : String → List PsCmd → PsCmd
  Index : ℕ → PsCmd
  FunCall : String → PsCmd
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

\begin{code}
Prog = String

emptyProg : Prog
emptyProg = ""
\end{code}

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

updateErr : (String → String) → ExtractM X → ExtractM X

liftTC : TC X → ExtractM X

markAsDone : Name → ExtractM ⊤
\end{code}

\begin{code}[hide]
fail err .runExtractM s = R.return (s , error err)

updateErr f m .runExtractM s = m .runExtractM s R.>>= λ where
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
pattern `index k s = def (quote index) (_ ∷ _ ∷ vArg k ∷ _ ∷ vArg s ∷ [])
pattern `subst-stack s = def (quote subst-stack) (_ ∷ _ ∷ _ ∷ _ ∷ vArg s ∷ [])

pattern `add s  = def (quote add) (_ ∷ vArg s ∷ [])
pattern `sub s  = def (quote sub) (_ ∷ vArg s ∷ [])
pattern `mul s  = def (quote mul) (_ ∷ vArg s ∷ [])
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
  updateErr (λ x → "variable does not match arg pattern: " S.++ x) (pat-match-term p v)
  return []

extract-term v@(_ `# _) p = do
  updateErr (λ x → "Stack constructor does not match arg pattern: " S.++ x) (pat-match-term p v)
  return []

extract-term (`add x) p = do
  b ← extract-term x p
  return (Add ∷ b)

extract-term (`pop x) p = do
  b ← extract-term x p
  return (Pop ∷ b)

extract-term (`sub x) p = do
  b ← extract-term x p
  return (Sub ∷ b)

extract-term (`mul x) p = do
  b ← extract-term x p
  return (Mul ∷ b)

extract-term (`exch x) p = do
  b ← extract-term x p
  return (Exch ∷ b)

extract-term (`index (lit (nat n)) x) p = do
  b ← extract-term x p
  return (Index n ∷ b)

extract-term (`index k x) p = do
  fail ("extract-term: index with non-literal " S.++ showTerm k)

-- We only support literals as an object that you can push.
extract-term (`push (lit (nat n)) x) p = do
  b ← extract-term x p
  return (Push n ∷ b)

extract-term (`push k x) p =
  fail ("extract-term: push with non-literal " S.++ showTerm k)

extract-term (`dup x) p = do
  b ← extract-term x p
  return (Dup ∷ b)

extract-term (`subst-stack x) p = do
  extract-term x p

extract-term (def fname args@(_ ∷ _)) p = do
  ty ← liftTC (getType fname)
  markAsDone fname
  n ← updateErr (λ x → "trying to obtain type of `" S.++ showName fname S.++ "` with: " S.++ x) (extract-function-type ty)
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

\begin{code}[hide]
record TyState : Set where
  pattern
  field
    pi-ok  : Bool
    sz-arg : Bool
    st-arg : Bool
\end{code}

The function \AgdaFunction{extract-type} defines what Agda types are valid
for functions in the embedding.  It also returns which argument
corresponds to the stack.

\begin{code}
extract-type : Type → (st : TyState) → (off : ℕ) → ExtractM ℕ

-- If we haven't seen size-argument, we can have it.
extract-type (Π[ s ∶ arg _ `ℕ ] y) st@record { sz-arg = false } o =
  extract-type y record st { sz-arg = true } (1 + o)

-- We can get a Stack argument in case we haven't seen it.
extract-type (Π[ s ∶ arg _ (`Stack X n) ] y) st@record { st-arg = false } o =
  -- We can have Stack without explicit size
  extract-type y record st { sz-arg = true; st-arg = true } o

-- We can get anything hidden and irrelevant before the Stack.
extract-type (Π[ s ∶ hArg0 _ ] y) st@record { st-arg = false } o =
  -- We increase the position here
  extract-type y st (1 + o)

-- We can get anything hidden and irrelevant after the Stack,
-- but then we do not increase the position of the argument.
extract-type (Π[ s ∶ hArg0 _ ] y) st@record { st-arg = true } o =
  extract-type y st o

-- Finally, the last argument, i.e. the return type can only
-- be Stack, given that we have seen st-arg.
extract-type (`Stack X n) record { st-arg = true } o = return o

extract-type t _ _ =
  fail ("failed with the type `" S.++ showTerm t S.++ "`")

extract-function-type x = extract-type x (record { pi-ok = true; sz-arg = false; st-arg = false }) 0
\end{code}

\begin{code}[hide]
lookup-pattern : List (Arg Pattern) → ℕ → ExtractM Pattern
lookup-pattern ((arg _ x) ∷ xs) zero = return x
lookup-pattern (_ ∷ xs) (suc n) = lookup-pattern xs n
lookup-pattern _ _ = fail "extract-clauses: invalid stack variable index in patterns"
\end{code}

\begin{code}
extract-pattern : (hd-idx : ℕ) → Pattern → ExtractM (List PsCmd × ℕ)
extract-pattern hd-idx (p₁ `#p p₂) = do
  (l₁ , n₁) ← hlpr p₂ hd-idx 0
  (l₂ , n₂) ← extract-pattern (hd-idx + n₁ + 1) p₁
  case n₁ + n₂ of λ where
    0 → return (l₁ ++ l₂ , 0)
    1 → return (l₁ ++ l₂ , 1)
    2 → return (l₁ ++ l₂ ++ [ And ] , 1)
    _ → fail "extract-pattern: impossible stack length"
 where
    hlpr : Pattern → (hd-idx suc-count : ℕ) → ExtractM (List PsCmd × ℕ)
    hlpr (var x) _      0 = return ([] , 0)
    hlpr (var x) hd-idx c = return (Index hd-idx ∷ Push c ∷ Ge ∷ [] , 1)
    hlpr (lit (nat x)) hd-idx sc = return (Index hd-idx ∷ Push (sc + x) ∷ Eq ∷ [] , 1)
    hlpr (`suc x) hd-idx c = hlpr x hd-idx (1 + c)
    hlpr `zero hd-idx c = return (Index hd-idx ∷ Push c ∷ Eq ∷ [] , 1)
    hlpr _ _ _ = fail "extract-pattern hlpr: Invalid pattern for ℕ argument"

extract-pattern _ (var x) = return ([] , 0)
extract-pattern _ _ = fail "extract-pattern: invalid stack pattern _,_ expected"
\end{code}

\begin{code}
extract-clauses [] num-arg = fail "extract-clauses: zero clauses found"
extract-clauses (clause _ ps t ∷ []) num-arg = do
  p ← lookup-pattern ps num-arg
  t ← extract-term t p
  return (L.reverse t)

extract-clauses (absurd-clause _ ps ∷ []) num-arg =
  return []

extract-clauses (absurd-clause _ ps ∷ ts@(_ ∷ _)) num-arg = do
  argp ← lookup-pattern ps num-arg
  (l , _) ← extract-pattern 0 argp
  ts ← extract-clauses ts num-arg
  return (l ++ [ IfElse [] ts ])

extract-clauses (clause _ ps t ∷ ts@(_ ∷ _)) num-arg = do
  argp ← lookup-pattern ps num-arg
  (l , _) ← extract-pattern 0 argp
  t ← extract-term t argp
  ts ← extract-clauses ts num-arg
  return (l ++ [ IfElse (L.reverse t) ts ])
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

_ : extract-stack-id ≡ "\n\n/extraction.stack-id {\n  \n} def\n"
_ = refl

extract-dblsuc = extract dblsuc base base

_ : extract-dblsuc ≡ "\n\n/extraction.add1 {\n  1 add\n} def\n\n\n/extraction.dblsuc {\n  dup extraction.add1\n} def\n"
_ = refl


extract-sqsum = extract sqsum base base

_ : extract-sqsum ≡ "\n\n/extraction.sqsum {\n  dup mul exch dup mul add\n} def\n"
_ = refl

extract-rep-simple =  extract RepSimple.rep base base

_ : extract-rep-simple ≡
  "\n\n/extraction.RepSimple.rep {\n  0 index 0 eq \n  {\n    pop pop\n  }\n  {\n    1 sub 1 index exch extraction.RepSimple.rep\n  } ifelse\n\n} def\n"
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
