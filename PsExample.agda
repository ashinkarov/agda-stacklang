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
open import Agda.Builtin.Reflection

open import Structures
open import Function

open import Data.Unit using (⊤; tt)
open import Data.Empty 

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


sqsum : ∀ {n} → Stack ℕ (2 + n) → Stack ℕ (1 + n)
sqsum s@(_ , a , b) =  add $ mul $ dup $ exch $ mul $ dup $ s

{-# TERMINATING #-}
fac : ∀ {n} → Stack ℕ (1 + n) → Stack ℕ (1 + n)
fac s@(_ , 0)     = push 1 $ pop $ s
fac s@(_ , suc n) = let
     sn:sn = dup s
     sn:n = sub $ push 1 $ sn:sn
     sn:fac[n] = fac $ sn:n
   in mul sn:fac[n]


sx≥₁x : ∀ {x} → suc x ≥₁ x
sx≥₁x {x} = next done


≥₁-prev : ∀ {x y} → suc x ≥₁ suc y → x ≥₁ y
≥₁-prev {x} {.x} done = done
≥₁-prev {x} {y} (next sx≥sy) = next (≥₁-prev sx≥sy)

x≥₁sy→x≥₁y : ∀ {x y} → x ≥₁ suc y → x ≥₁ y
x≥₁sy→x≥₁y done = next done
x≥₁sy→x≥₁y (next x≥sy) = next (x≥₁sy→x≥₁y x≥sy)

≥₁→≥ : ∀ {x y} → x ≥₁ y → x ≥ y
≥₁→≥ {x} {.x} done = ≤-refl
≥₁→≥ {x} {y} (next x≥y) = hlpr (≥₁→≥ x≥y)
  where
    hlpr : ∀ {x y} → x ≥ suc y → x ≥ y
    hlpr {suc x} {zero} (s≤s x≥sy) = z≤n
    hlpr {suc x} {suc y} (s≤s x≥sy) = s≤s (hlpr x≥sy)

0≥₁suc : ∀ {x} → 0 ≥₁ suc x → ⊥
0≥₁suc {x} (0≥sx) with (≥₁→≥ 0≥sx)
... | ()

cong-≥₁ : ∀ {x y} → x ≥₁ y → suc x ≥₁ suc y
cong-≥₁ {x} {.x} done = done
cong-≥₁ {x} {y} (next x≥y) = next (cong-≥₁ x≥y)

x≥₁y→s[x]≥₁y : ∀ {x y} → x ≥₁ y → suc x ≥₁ y
x≥₁y→s[x]≥₁y {x} {.x} done = next done
x≥₁y→s[x]≥₁y {x} {y} (next x≥₁y) = next (x≥₁y→s[x]≥₁y x≥₁y)

≥₁-trans : ∀ {x y z} → x ≥₁ y → y ≥₁ z → x ≥₁ z
≥₁-trans {x} {y} {.y} x≥y done = x≥y
≥₁-trans {x} {y} {z} x≥y (next y≥z) = x≥₁sy→x≥₁y (≥₁-trans x≥y y≥z)


x≥₁0 : ∀ {x} → x ≥₁ 0
x≥₁0 {zero} = done
x≥₁0 {suc x} = ≥₁-trans sx≥₁x x≥₁0 

count-0-thm : ∀ {x y} → (p : x ≥₁ y) → count p 0 ≡ 0
count-0-thm done = refl
count-0-thm (next p) rewrite +-identityʳ (count p 0) = count-0-thm p

sum-for : ∀ {n} → Stack ℕ (1 + n) → Stack ℕ (1 + n)
sum-for {n} s@(_ , x) = let
  xx = for {l = 0}{k = 1} (exch $ push 0 $ exch $ push 10 $ s) {x≥₁0} foo
  in subst-stack cast-for xx
  where
    cast-for : suc (count {a = x} x≥₁0 0 + n) ≡ suc n
    cast-for rewrite count-0-thm {x = x} x≥₁0 = refl

    foo : ∀ {m} → Stack ℕ (2 + m) → Stack ℕ (1 + m)
    foo {m} s = push 1 $ pop $ pop s -- add s

fib-for : ∀ {n} → Stack ℕ (1 + n) → Stack ℕ (1 + n)
fib-for {n} s@(_ , x) = let
  init  = exch $ push 0 $ exch $ push 1 $ exch $ push 1 $ s
  s:x:y = subst-stack cast-for $ for {l = 0}{k = 2} init {x≥₁0} foo
  in pop s:x:y
  where
    cast-for : suc (suc (count {a = x} x≥₁0 0 + n)) ≡ suc (suc n)
    cast-for rewrite count-0-thm {x = x} x≥₁0 = refl

    foo : ∀ {m} → Stack ℕ (3 + m) → Stack ℕ (2 + m)
    foo s = add $ index {m = 2} 1 (s≤s (s≤s z≤n)) $ exch $ pop s


module Sierpinski where
    -- 0 1 n {
    --   0 1 n {
    --      2 copy and 0 eq
    --      {
    --        2 copy .3 0 360 arc fill
    --      } if
    --      pop
    --  } for 
    --  pop
    -- } for
    postulate
      draw-circ-xy : ∀ {n} → Stack ℕ (2 + n) → Stack ℕ n
      bit-and : ∀ {n} → Stack ℕ (2 + n) → Stack ℕ (1 + n)

    -- At runtime we need to add these definitions:
    -- /PsExample.Sierpinski.draw-circ-xy {
    --     .3 0 360 arc fill
    -- } def
    -- /PsExample.Sierpinski.bit-and  {
    --     and
    -- } def

    cast-for : ∀ {k n x} → k + (count {a = x} x≥₁0 0 + n) ≡ k + n
    cast-for {x = x} rewrite count-0-thm {x = x} x≥₁0 = refl


    draw-if : ∀ {n} → Stack ℕ (3 + n) → Stack ℕ (2 + n)
    draw-if s@(_ , x , y , 0) =  
            draw-circ-xy 
            $ index {m = 2} 1 (s≤s (s≤s z≤n)) 
            $ index {m = 2} 1 (s≤s (s≤s z≤n)) 
            $ pop s
    draw-if s = pop s

    inner-for-loop : ∀ {m} → Stack ℕ (2 + m) → Stack ℕ (1 + m)
    inner-for-loop s:x:i:j = let
      s:x:i:j:i&j = bit-and 
                    $ index {m = 2} 1 (s≤s (s≤s z≤n)) 
                    $ index {m = 2} 1 (s≤s (s≤s z≤n)) 
                    $ s:x:i:j
      cond-draw = draw-if s:x:i:j:i&j
      in pop cond-draw

    outer-for-loop : ∀ {m} → Stack ℕ (2 + m) → Stack ℕ (1 + m)
    outer-for-loop {m} s:x:i@(_ , x , _) = let
      s:x:i:0:x = index {m = 3} 2 (s≤s (s≤s (s≤s z≤n))) $ push 0 $ s:x:i
      res-for = for {l = 0}{k = 1} s:x:i:0:x {x≥₁0} inner-for-loop
      in subst-stack (cast-for {0}{suc m}{x = x}) $ pop $ res-for

    sierp : ∀ {n} → Stack ℕ (1 + n) → Stack ℕ n
    sierp {n} s@(_ , x) = let
      s:x:0:x = index {m = 2} 1 (s≤s (s≤s z≤n)) $ push 0 $ s
      res-for = for {l = 0}{k = 1} s:x:0:x {x≥₁0} outer-for-loop
      in subst-stack (cast-for {0}{n}{x}) $ pop $ res-for

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

module Fib3 where
    fib3 : ∀ {n}{@0 y : ℕ} → (s : Stack ℕ (3 + n)) 
         → {@0 _ : get-index {n = n} 2 (s≤s (s≤s (s≤s z≤n))) s < y} 
         → Stack ℕ (3 + n)
    fib3 s@(_ , 0 , a , b ) = s
    fib3 {y = .suc y} s@(_ , (suc m) , a , b) {s≤s m<y} = let
      s:sm:a:b = s
      s:sm:b:a+b = add $ index {m = 2} 1 (s≤s (s≤s z≤n)) $ exch s:sm:a:b
      s:a+b:b:m = sub $ push 1 $ rot3 s:sm:b:a+b
      s:m:b:a+b = rot3 s:a+b:b:m
      in fib3 s:m:b:a+b {m<y}

    fib : ∀ {n} → Stack ℕ (1 + n) → Stack ℕ (1 + n)
    fib s@(_ , m) = let
      s:m:0:1 = push 1 $ push 0 $ s
      s:fibm = pop $ exch $ pop $ fib3 s:m:0:1 {≤-refl}
      in s:fibm

module FibNoSplit where

  -- XXX This is another way of proving termination, but it is rather ugly.
  --     If we want to extract it, we need to teach extractor about SProp and
  --     its constructors.
  infixl 3 _#_
  -- Stack with an irrelevant property
  record SProp (X : Set) (n : ℕ) (P : Stack X n → Set) : Set where
    constructor _#_
    field
      st : Stack X n
      @0 p : P st

  fib′ : ∀ {@0 y} {n} → (s : Stack ℕ (1 + n)) → @0 (hd s < y) → SProp ℕ (1 + n) (λ s' → tl s' ≡ tl s)
  fib′ (xs , 0) _ = (xs , 1) # refl
  fib′ (xs , 1) _ = (xs , 1) # refl
  fib′ {.suc y} {n} xs@(l , r@(suc (suc x))) (s≤s x<y) =
     let
       l:r:r-1             = sub $ push 1 $ dup xs
       l:r:fib[r-1]        = fib′ l:r:r-1 x<y
       l:fib[r-1]:r        : SProp ℕ _ λ s' → hd s' ≡ suc (suc x) × tl (tl s') ≡ l
       l:fib[r-1]:r        = (exch $ SProp.st l:r:fib[r-1])
                             #  (exch-hd {xs = SProp.st l:r:fib[r-1]} $ SProp.p l:r:fib[r-1])
                             ,, (exch-tl {xs = SProp.st l:r:fib[r-1]} $ SProp.p l:r:fib[r-1])
       l:fib[r-1]:r-2      : SProp ℕ _ λ s' → hd s' ≡ x × tl (tl s') ≡ l
       l:fib[r-1]:r-2      = (sub $ push 2 $ SProp.st l:fib[r-1]:r)
                             #  sub2-hd {xs = SProp.st l:fib[r-1]:r} (proj₁ $ SProp.p l:fib[r-1]:r)
                             ,, sub2-tl {xs = SProp.st l:fib[r-1]:r} (proj₂ $ SProp.p l:fib[r-1]:r)
       l:fib[r-1]:fib[r-2] = fib′ (SProp.st l:fib[r-1]:r-2)
                                  (subst (_< y) (sym $ proj₁ $ SProp.p l:fib[r-1]:r-2) (<-trans ≤-refl x<y))
     in (add $ SProp.st l:fib[r-1]:fib[r-2])
        # (add-tl {xs = SProp.st l:fib[r-1]:fib[r-2]}
                  {ys = SProp.st l:fib[r-1]:r-2}
                  (SProp.p l:fib[r-1]:fib[r-2])
                  (proj₂ $ SProp.p l:fib[r-1]:r-2))
   where
    exch-tl : ∀ {X : Set}{n}{xs : Stack X (2 + n)}{x}{ys} → tl xs ≡ (ys , x) → tl (tl (exch xs)) ≡ ys
    exch-tl {xs = _ , _ , _} refl = refl

    exch-hd : ∀ {X : Set}{n}{xs : Stack X (2 + n)}{x}{ys} → tl xs ≡ (ys , x) → hd (exch xs) ≡ x
    exch-hd {xs = _ , _ , _} refl = refl

    sub2-hd : ∀ {n}{xs : Stack ℕ (2 + n)}{x} → hd xs ≡ suc (suc x) → hd (sub $ push 2 $ xs) ≡ x
    sub2-hd {xs = _ , _} refl = refl

    sub2-tl : ∀ {n}{xs : Stack ℕ (2 + n)}{ys} → tl (tl xs) ≡ ys → tl (tl (sub $ push 2 $ xs)) ≡ ys
    sub2-tl {xs = _ , _ , _} refl = refl

    add-tl : ∀ {n}{xs : Stack ℕ (2 + n)}{ys}{zs} → tl xs ≡ tl ys → tl (tl ys) ≡ zs → tl (add xs) ≡ zs
    add-tl {xs = _ , _ , _} {ys = _ , _ , _} refl refl = refl


base = quote add ∷ quote sub ∷ quote dup ∷ quote push ∷ quote pop 
     ∷ quote index ∷ quote subst-stack ∷ quote exch ∷ quote rot3 
     ∷ quote iframep ∷ quote for ∷ []


base-sierp = quote Sierpinski.bit-and ∷ quote Sierpinski.draw-circ-xy ∷ base
ktest-sierp : Prog
ktest-sierp = kompile Sierpinski.sierp base-sierp base-sierp

ktest-for : Prog
ktest-for = kompile sum-for base base

ktest-fibfor : Prog
ktest-fibfor = kompile fib-for base base

ktest₁ = kompile stack-id base base
test₁ : ok _ ≡ ktest₁
test₁ = refl

ktest₂ = kompile dblsuc base base
test₂ : ok _ ≡ ktest₂
test₂ = refl

ktest₂₁ = kompile sqsum base base
test₂₁ : ok _ ≡ ktest₂₁
test₂₁ = refl

ktest₂₂ = kompile fac base base
test₂₂ : ok _ ≡ ktest₂₂
test₂₂ = refl

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

ktest₆ : Prog
ktest₆ = kompile FibTerm.fib base base
test₆ : ok _ ≡ ktest₆
test₆ = refl

ktest₇ : Prog
ktest₇ = kompile Fib3.fib base base
test₇ : ok _ ≡ ktest₇
test₇ = refl

