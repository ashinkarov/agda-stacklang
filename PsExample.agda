open import PostScriptLang as P
open import Extract (P.kompile-funp) using (kompile)
open import ReflHelper

open import Data.Nat
open import Data.Nat.Properties
open import Data.List as L using (List; []; _∷_)
open import Data.Product renaming (_,_ to _,,_)

--open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Reflection -- hiding (_≟_; _>>=_; return)
--open import Agda.Builtin.Reflection

open import Structures
open import Function

open import Data.Unit

open import ps as PostScript


-- This function does nothing to the stack but it introduces
-- a bunch of runtime irrelevant argumetns.
stack-id : ∀ {@0 m : ℕ} → (s : Stack ℕ 1) → {@0 b : m > 0} → Stack ℕ 1
stack-id xs@(t , h) = (t , 0 + h)


-- These two functions demonstrate a trivial case when one function
-- calls another function.
add1 : ∀ {n} → Stack ℕ (1 + n) → Stack ℕ (1 + n)
add1 xs = sub $ push 1 $ xs

dblsuc : ∀ {n} → Stack ℕ (1 + n) → Stack ℕ (2 + n)
dblsuc xs = add1 $ dup xs

-- The `rep` function is the simplest example of
-- using dependent types in a stack function.  `rep` [ x n ]
-- replicates `x` `n` times, so we obtain [ x x x ... ]
module RepSimple where
    {-# TERMINATING #-}
    rep : ∀ {n} → (s : Stack ℕ (2 + n)) → Stack ℕ (hd s + n)
    rep {n} xs@(_ , _ , zero)      = pop $ pop xs
    rep {n} xs:x:m+1@(_ , _ , m@(suc _)) = 
           let
             xs:x:m   = sub $ push 1 xs:x:m+1 
             xs:x:m:x = index {m = 2} 1 ≤-refl $ xs:x:m
             xs:x:x:m = exch xs:x:m:x
           in subst-stack (+-suc _ _) $ rep {n = suc n} xs:x:x:m

module RepTerm where
    rep′ : ∀ {n}{@0 y} → (s : Stack ℕ (2 + n)) → {@0 _ : hd s < y} → Stack ℕ (hd s + n)
    rep′ {n} xs@(_ , _ , zero)      = pop $ pop xs
    rep′ {n} xs:x:m+1@(_ , _ , m@(suc _)) { s≤s hd[s]<y } = let
             xs:x:m   = sub $ push 1 xs:x:m+1
             xs:x:m:x = index {m = 2} 1 ≤-refl $ xs:x:m
             xs:x:x:m = exch xs:x:m:x
           in subst-stack (+-suc _ _) $ rep′ {n = suc n} xs:x:x:m {hd[s]<y}

    rep : ∀ {n} → (s : Stack ℕ (2 + n)) → Stack ℕ (hd s + n)
    rep s = rep′ s {≤-refl}


module FibNonTerm where
  {-# TERMINATING #-}
  fib : ∀ {n} → Stack ℕ (1 + n) → Stack ℕ (1 + n)
  fib xs@(_ , 0)             = push 1 $ pop xs
  fib xs@(_ , 1)             = push 1 $ pop xs
  fib xs@(_ , suc (suc x))   = add $ fib $ sub $ push 2 $ exch $ fib $ sub $ push 1 $ dup xs



module FibTerm where
  fib′ : ∀ {@0 y n} → (s : Stack ℕ (1 + n)) → @0 {hd s < y} → Stack ℕ (1 + n)
  fib′ xs@(_ , 0) = push 1 $ pop xs --xs , 1
  fib′ xs@(_ , 1) = push 1 $ pop xs -- xs , 1
  fib′ {.suc y} xs@(l , r@(suc (suc x))) { s≤s x<y } =
    let
      l:r:r-1        = sub $ push 1 $ dup xs
      l:r:fib[r-1]   = iframep {m = 1} {P = λ s → suc x ≡ hd s}
                              (λ s hd[s]≡suc[x] → fib′ s { subst (_< y) hd[s]≡suc[x] x<y })
                              l:r:r-1 refl
      l:fib[r-1]:r-2 = sub $ push 2 $ exch l:r:fib[r-1]
    in                 add $ fib′ l:fib[r-1]:r-2
                                  { fib-thm {ys =  fib′ ([] , suc x)} (<-trans ≤-refl x<y) }
   where
    fib-thm : ∀ {n}{xs : Stack ℕ n}{ys : Stack ℕ 1}{x}{l} 
            → x < l → hd (sub $ (exch ((xs , suc (suc x)) PostScript.++ ys) , 2)) < l
    fib-thm {ys = [] , y} x<l = x<l

  fib : ∀ {n} → Stack ℕ (1 + n) → Stack ℕ (1 + n)
  fib xs = fib′ xs {≤-refl}


base = quote add ∷ quote sub ∷ quote dup ∷ quote push ∷ quote pop 
     ∷ quote index ∷ quote subst-stack ∷ quote exch ∷  []



ktest₁ = kompile stack-id base base
test₁ : ok _ ≡ ktest₁
test₁ = refl

ktest₂ = kompile dblsuc base base
test₂ : ok _ ≡ ktest₂
test₂ = refl

ktest₃ : Prog
ktest₃ = kompile RepSimple.rep base base
test₃ : ok _ ≡ ktest₃
test₃ = refl

ktest₄ = kompile RepTerm.rep base base
test₄ : ok _ ≡ ktest₄
test₄ = refl

ktest₅ = kompile FibNonTerm.fib base base
test₅ : ok _ ≡ ktest₅
test₅ = refl

-- XXX this doesn't work yet because of iframep.
ktest₆ : Prog
ktest₆ = kompile FibTerm.fib base base
