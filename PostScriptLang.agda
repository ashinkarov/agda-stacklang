-- {-# OPTIONS --safe #-}
open import Structures

open import Data.String using (String; _≈?_)
open import Data.List as L using (List; []; _∷_; [_])
open import Data.List.Categorical
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_)
import Data.Nat.Properties as ℕ
open import Data.Nat.DivMod
open import Agda.Builtin.Nat using (div-helper; mod-helper)
open import Data.Nat.Show using () renaming (show to showNat)
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.Fin as F using (Fin; zero; suc; #_)

open import Category.Monad
open import Category.Monad.State

open import Data.Product as Σ
open import Data.Unit
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin using (Fin; zero; suc; fromℕ<)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import Relation.Nullary

open import Reflection hiding (return; _>>=_; _>>_)
open import Reflection.Term
import      Reflection.Name as RN
open import Function
open import Strict

open import ps as PostScript using (Stack)

open RawMonad ⦃ ... ⦄


data PsCmd : Set where
  Push : ℕ → PsCmd
  Dup Add Mul Eq Ge And Pop Sub Exch Rot3 : PsCmd
  If : List PsCmd → PsCmd  
  IfElse : List PsCmd → List PsCmd → PsCmd
  FunDef : String → List PsCmd → PsCmd
  Index : ℕ → PsCmd
  FunCall : String → PsCmd

Expr = PsCmd

indent : ℕ → String
indent n = "" ++/ L.replicate n "  "

lexpr-to-string : (ind : ℕ) → List Expr → List String

expr-to-string : (ind : ℕ) → Expr → String
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
                           ++ indent ind ++ "{\n"
                           ++ indent ind ++ " " ++/ lexpr-to-string (1 + ind) xs ++ "\n"
                           ++ indent ind ++"\n} if\n"
expr-to-string ind (FunDef n xs) = indent ind ++ "/" ++ n ++ " {\n"
                                ++ indent (1 + ind) ++ " " ++/ lexpr-to-string (1 + ind) xs ++ "\n"
                                ++ indent ind ++ "} def\n"
expr-to-string ind (Index x) = showNat x ++ " index"
expr-to-string ind (FunCall x) = x
expr-to-string ind (IfElse xs ys) = "\n"
                                 ++ indent ind ++ "{\n"
                                 ++ indent (1 + ind) ++ " " ++/ lexpr-to-string (1 + ind) xs ++ "\n"
                                 ++ indent ind ++ "}\n"
                                 ++ indent ind ++ "{\n"
                                 ++ indent (1 + ind) ++ " " ++/ lexpr-to-string (1 + ind) ys ++ "\n"
                                 ++ indent ind ++ "} ifelse\n"

-- XXX we can improve the indentation by casing in the list-printing function
--     so that we can insert newlines in a more controlled fashion.
lexpr-to-string ind [] = []
lexpr-to-string ind (x ∷ xs) = expr-to-string ind x ∷ lexpr-to-string ind xs



kompile-fun    : Type → Term → Name → TCS $ Err Expr
kompile-pi     : Type → Err ℕ
kompile-cls    : Clauses → ℕ → TCS $ Err $ List Expr
{-# TERMINATING #-}
kompile-term   : Term → (stack-arg-pat : Pattern) → TCS $ Err $ List Expr



kompile-funp   : Type → Term → Name → TCS Prog
kompile-funp ty te n = do
  (ok e) ← kompile-fun ty te n where (error x) → return $ error x
  return $ ok $ expr-to-string 0 e


private
  kf : String → Err Expr
  kf x = error $ "kompile-fun: " ++ x

  module RR = RawMonadState (StateTMonadState KS monadTC)
  
  emap : ∀ {a b}{X : Set a}{Y : Set b} → (X → Y) → Err X → Err Y
  emap f (error x) = error x
  emap f (ok x) = ok $ f x

  _>>=e_ : ∀ {a}{X : Set a}{Y} → Err X → (X → TCS $ Err Y) → TCS $ Err Y
  (error s) >>=e _ = return $ error s
  (ok x)    >>=e f = f x


kompile-fun ty (pat-lam [] []) n =
  return $ kf "got zero clauses in a lambda term"

kompile-fun ty (pat-lam cs []) fname = do
  b ← kompile-pi ty >>=e kompile-cls cs
  return $ emap (FunDef $ showName fname) b

kompile-fun _ _ _ =
  return $ kf "expected pattern-matching lambda"


record TyState : Set where
  pattern
  field
    pi-ok  : Bool
    sz-arg : Bool
    st-arg : Bool

kompile-ty : Type → (st : TyState) → (off : ℕ) → Err ℕ

-- If we haven't seen size-argument, we can have it.
kompile-ty (Π[ s ∶ (hArg (def (quote ℕ) [])) ] y) st@record { sz-arg = false } o =
  kompile-ty y record st { sz-arg = true } (1 + o)

-- We can get a Stack argument in case we haven't seen it.
kompile-ty (Π[ s ∶ (vArg (def (quote Stack) _)) ] y) st@record { st-arg = false } o = 
  -- We can have Stack without explicit size
  kompile-ty y record st { sz-arg = true; st-arg = true } o

-- We can get anything hidden and irrelevant before the Stack.
kompile-ty (Π[ s ∶ arg (arg-info hidden (modality r quantity-0)) _ ] y) st@record { st-arg = false } o =
  -- We increase the position here
  kompile-ty y st (1 + o)

-- We can get anything hidden and irrelevant after the Stack,
-- but then we do not increase the position of the argument.
kompile-ty (Π[ s ∶ arg (arg-info hidden (modality r quantity-0)) _ ] y) st@record { st-arg = true } o =
  kompile-ty y st o

-- Finally, the last argument, i.e. the return type can only
-- be Stack, given that we have seen st-arg.
kompile-ty (def (quote Stack) args) record { st-arg = true } o =
  ok o

kompile-ty t _ _ =
  error $ "failed with the type `" ++ showTerm t ++ "`"

kompile-pi x = kompile-ty x record { pi-ok = true; sz-arg = false; st-arg = false } 0




private
  kc : String → TCS $ Err $ List Expr
  kc x = return $ error $ "kompile-cls: " ++ x

index-pat : List (Arg Pattern) → ℕ → Err Pattern
index-pat ((arg _ x) ∷ xs) zero = ok x
index-pat (_ ∷ xs) (suc n) = index-pat xs n
index-pat _ _ = error "kompile-pat: invalid stack variable index in patterns"


pat-to-expr : Pattern → (hd-idx : ℕ) → Err $ List Expr × ℕ
pat-to-expr (con (quote Stack._,_) (hArg h ∷ vArg p₁ ∷ vArg p₂ ∷ [])) hd-idx = do
  (l₁ , n₁) ← hlpr p₂ hd-idx 0
  (l₂ , n₂) ← pat-to-expr p₁ (hd-idx + n₁ + 1)
  case n₁ + n₂ of λ where
    0 → ok $ l₁ ++ l₂ , 0
    1 → ok $ l₁ ++ l₂ , 1
    2 → ok $ l₁ ++ l₂ ++ [ And ] , 1
    _ → error "pat-to-expr: impossible stack length"
 where
    hlpr : Pattern → (hd-idx suc-count : ℕ) → Err $ List Expr × ℕ
    hlpr (var x) _      0 = ok $ [] , 0
    hlpr (var x) hd-idx c = ok $ Index hd-idx ∷ Push c ∷ Ge ∷ [] , 1
    hlpr (lit (nat x)) hd-idx sc = ok $ Index hd-idx ∷ Push (sc + x) ∷ Eq ∷ [] , 1
    hlpr (con (quote ℕ.suc) (vArg x ∷ [])) hd-idx c = hlpr x hd-idx (1 + c)
    hlpr (con (quote ℕ.zero) _) hd-idx c = ok $ Index hd-idx ∷ Push c ∷ Eq ∷ [] , 1
    hlpr _ _ _ = error "pat-to-expr hlpr: Invalid pattern for ℕ argument"

pat-to-expr (var x) _ = ok $ [] , 0
pat-to-expr _ _ = error "pat-to-expr: invalid stack pattern _,_ expected"


patnat-to-nat : Pattern → Err ℕ
patnat-to-nat (con (quote ℕ.zero) []) = ok 0
patnat-to-nat (con (quote ℕ.suc) (vArg x ∷ [])) = suc <$> patnat-to-nat x
patnat-to-nat _ = error "not a suc/zero pattern"


term-to-nat : Term → Err ℕ
term-to-nat (con (quote ℕ.zero) []) = ok 0
term-to-nat (con (quote ℕ.suc) (vArg x ∷ [])) = suc <$> term-to-nat x
term-to-nat _ = error "not a suc/zero term"

pat-match-term : Pattern → Term → TCS $ Err ⊤
pat-match-term p@(con (quote Stack._,_) (hArg _          ∷ vArg p₁ ∷ vArg p₂ ∷ []))
               t@(con (quote Stack._,_) (hArg _ ∷ hArg _ ∷ vArg t₁ ∷ vArg t₂ ∷ [])) = do
  (ok _) ← pat-match-term p₁ t₁ where (error x) → return $ error x
  (ok _) ← pat-match-term p₂ t₂ where (error x) → return $ error x
  return $ ok _ 

pat-match-term (var x) (var y []) with x ℕ.≟ y
... | yes _ = return $ ok _
... | no  _ = return $ error "pat-match-term: variables do not match"

pat-match-term (lit (nat x)) (lit (nat y)) with x ℕ.≟ y
... | yes _ = return $ ok _
... | no  _ = return $ error "pat-match-term: literal vaues do not match"

pat-match-term (con (quote ℕ.zero) []) (con (quote ℕ.zero) []) = return $ ok _
--pat-match-term (lit (nat 0)) (con (quote ℕ.zero) []) = return $ ok _
--pat-match-term (con (quote ℕ.zero) []) (lit (nat 0)) = return $ ok _

pat-match-term (con (quote ℕ.suc) (vArg x ∷ [])) (con (quote ℕ.suc) (vArg y ∷ [])) =
    pat-match-term x y

pat-match-term (lit (nat x)) y {- @(con (quote ℕ.suc) (vArg _ ∷ [])) -} = do
  (ok y′) ← return $ term-to-nat y
    where (error x) → return $ error x
  return $ case x ℕ.≟ y′ of λ where
    (yes _) → ok _
    (no  _) → error "pat-match-term: invalid literal/number match"

pat-match-term x {- @(con (quote ℕ.suc) (vArg _ ∷ [])) -} (lit (nat y)) = do
  (ok x′) ← return $ patnat-to-nat x
    where (error x) → return $ error x
  return $ case x′ ℕ.≟ y of λ where
    (yes _) → ok _
    (no  _) → error "pat-match-term: invalid literal/number match"


pat-match-term p t = return $ error 
                   $ "pat-match-term: invalid stack variable pattern: "
                   ++ showPattern p ++ " and " ++ showTerm t


kompile-cls [] num-arg = kc "zero clauses found"
kompile-cls (clause _ ps t ∷ []) num-arg = do
  t ← index-pat ps num-arg >>=e kompile-term t
  return $ L.reverse <$> t

kompile-cls (absurd-clause _ ps ∷ []) num-arg =
  return $ ok []

kompile-cls (absurd-clause _ ps ∷ ts@(_ ∷ _)) num-arg = do
  let argp = index-pat ps num-arg
  let l = join $ (flip pat-to-expr 0) <$> argp
  ts ← kompile-cls ts num-arg
  return $ (λ l ts → l ++ [ IfElse [] ts ]) <$> (proj₁ <$> l) ⊛ ts

kompile-cls (clause _ ps t ∷ ts@(_ ∷ _)) num-arg = do
  let argp = index-pat ps num-arg
  let l = join $ (flip pat-to-expr 0) <$> argp
  t ← argp >>=e kompile-term t
  ts ← kompile-cls ts num-arg
  return $ (λ l t ts → l ++ [ IfElse (L.reverse t) ts ]) <$> (proj₁ <$> l) ⊛ t ⊛ ts

--kompile-cls _ num_arg = kc "kompile-cls"



private
  kt : ∀ {X} → String → TCS $ Err X
  kt x = return $ error $ "kompile-term: " ++ x


kompile-term v@(var x []) p = do
  (ok _) ← pat-match-term p v where (error x) → kt "variable does not match arg pattern"
  return $ ok []

kompile-term v@(con (quote Stack._,_) _) p = do
  (ok _) ← pat-match-term p v 
      where (error x) → kt $ "Stack constructor does not match arg pattern: " ++ x
  return $ ok []

kompile-term (def (quote PostScript.add) args@(arg _ _ ∷ arg _ x ∷ [])) p = do
  b ← kompile-term x p
  return $ Add ∷_ <$> b

kompile-term (def (quote PostScript.mul) args@(arg _ _ ∷ arg _ x ∷ [])) p = do
  b ← kompile-term x p
  return $ Mul ∷_ <$> b

kompile-term (def (quote PostScript.pop) args@(_ ∷ _ ∷ vArg x ∷ [])) p = do
  b ← kompile-term x p
  return $ Pop ∷_ <$> b

kompile-term (def (quote PostScript.sub) args@(_ ∷ vArg x ∷ [])) p = do
  b ← kompile-term x p
  return $ Sub ∷_ <$> b

kompile-term (def (quote PostScript.exch) args@(_ ∷ _ ∷ vArg x ∷ [])) p = do
  b ← kompile-term x p
  return $ Exch ∷_ <$> b

kompile-term (def (quote PostScript.rot3) args@(_ ∷ _ ∷ vArg x ∷ [])) p = do
  b ← kompile-term x p
  return $ Rot3 ∷_ <$> b

kompile-term (def (quote PostScript.index) args@(_ ∷ _ ∷ _ ∷ vArg (lit (nat n)) ∷ _ ∷ vArg x ∷ [])) p = do
  b ← kompile-term x p
  return $ Index n ∷_ <$> b

-- We only support literals as an object that you can push.
kompile-term (def (quote PostScript.push) args@(_ ∷ _ ∷ vArg (lit (nat n)) ∷ vArg x ∷ [])) p = do
  b ← kompile-term x p
  return $ Push n ∷_ <$> b

kompile-term (def (quote PostScript.dup) args@(_ ∷ _ ∷ arg _ x ∷ [])) p = do
  b ← kompile-term x p
  return $ Dup ∷_ <$> b

kompile-term (def (quote PostScript.subst-stack) args@(_ ∷ _ ∷ _ ∷ _ ∷ vArg x ∷ [])) p = do
  kompile-term x p


kompile-term (def (quote PostScript.iframep) 
              args@(_₁ ∷ _₂ ∷ _₃ ∷ _₄ ∷ _₅ ∷ 
                    (vArg (vLam _ (vLam _ b))) ∷ arg _ x ∷ _)) p = do
  a ← kompile-term x p
  -- We assume that the application to iframep has been normalised to
  -- `λ s pf → body`, in which case, we should be able to kompile the
  -- term `body` with the pattern `var 1` (the first argument of the lambda).
  -- After that we can simply "apply" the extracted body to the argument `x`
  -- of iframep.
  f ← kompile-term b (var 1)
  return $ _++_ <$> f ⊛ a


kompile-term (def fname args@(_ ∷ _)) p = do
  ty ← lift-state {RM = monadTC} (getType fname)
  RR.modify λ k → record k { funs = KS.funs k ++ [ fname ] }
  (ok n) ← return $ kompile-pi ty -- defaultPS -- XXX maybe with updated KS
    where (error x) → return $ error $ "trying to obtain type of `" 
                                        ++ showName fname ++ "` with: " ++  x
  (ok (arg i a)) ← return $ index-args args n
     where (error x) → return $ error x
  b ← kompile-term a p
  return $ FunCall (showName fname) ∷_ <$> b
  where
    index-args : List (Arg Term) → ℕ → Err (Arg Term)
    index-args (a ∷ as) 0       = ok a
    index-args (a ∷ as) (suc i) = index-args as i
    index-args _ _ = error $ "index-args: wrong number of arguments to " ++ showName fname


kompile-term t vctx = kt $ "failed to compile term `" ++ showTerm t ++ "`"
