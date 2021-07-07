--{-# OPTIONS --irrelevant-projections #-}
{-# OPTIONS --safe #-}
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)
open import Function
open import Data.Unit

infixl 5 _,_
data Stack (X : Set) : @0 ℕ → Set where
  []  : Stack X 0
  _,_ : ∀ {n} → Stack X n → X → Stack X (suc n)

dup : ∀ {X n} → Stack X (suc n) → Stack X (suc (suc n))
dup (xs , x) = xs , x , x

exch : ∀ {X n} → Stack X (2 + n) → Stack X (2 + n)
exch (xs , x , y) = xs , y , x

add : ∀ {n} → Stack ℕ (2 + n) → Stack ℕ (1 + n)
add (xs , x , y) = xs , x + y

mul : ∀ {n} → Stack ℕ (2 + n) → Stack ℕ (1 + n)
mul (xs , x , y) = xs , x * y

sub : ∀ {n} → Stack ℕ (2 + n) → Stack ℕ (1 + n)
sub (xs , x , y) = xs , x ∸ y

push : ∀ {X n} → X → Stack X n → Stack X (1 + n)
push x xs = xs , x

eq : ∀ {n} → Stack ℕ (2 + n) → Stack ℕ (1 + n)
eq (xs , x , y) with x ≡ᵇ y
... | true  = xs , 1
... | false = xs , 0

pop : ∀ {X}{n} → Stack X (1 + n) → Stack X n
pop (xs , x) = xs

rot3 : ∀ {X n} → Stack X (3 + n) → Stack X (3 + n)
rot3 (s , a , b , c) =  s , c , b , a

get-index : ∀ {X}{m n} → (k : ℕ) → (@0 _ : k < m) → Stack X (m + n) → X
get-index {m = zero} k () xs
get-index {m = suc m} zero (s≤s k<m) (xs , x) = x
get-index {m = suc m} (suc k) (s≤s k<m) (xs , x) = get-index k k<m xs

index : ∀ {X}{m n} → (k : ℕ) → (@0 _ : k < m) → Stack X (m + n)  → Stack X (1 + m + n)
index k k<m xs = xs , get-index k k<m xs

subst-stack : ∀ {X}{@0 n m} → m ≡ n → Stack X m → Stack X n
subst-stack refl xs = xs

-- For loop
data _≥₁_ (l : ℕ) : ℕ → Set where
  done : l ≥₁ l
  next : ∀ {m} → l ≥₁ (suc m) → l ≥₁ m

count : ∀ {a b} → a ≥₁ b → (n : ℕ) → ℕ
count done      n = n
count (next qq) n = count qq n + n

for : ∀ {n l} 
    → (s : Stack ℕ (2 + n)) 
    → {geq : get-index {n = n} 0 (s≤s z≤n) s ≥₁ get-index {n = n} 1 (s≤s (s≤s z≤n)) s }
    → (∀ {m} → Stack ℕ (1 + m) → Stack ℕ (l + m)) 
    → Stack ℕ (count geq l + n)
for (s , i , .i) {done}    f = f (s , i)
for {n} {ll} (s , i , l)  {next qq} f = subst-stack (sym $ +-assoc _ ll n) (for (f (s , i) , suc i , l) {qq} f)


hd : ∀ {X n} → Stack X (1 + n) → X
hd (_ , x) = x

tl : ∀ {X n} → Stack X (1 + n) → Stack X n
tl (xs , _) = xs

_++_ : ∀ {X m n} → Stack X m → Stack X n → Stack X (n + m)
xs ++ [] = xs
xs ++ (ys , y) = xs ++ ys , y


split : ∀ {X}{n} → (m : ℕ) → Stack X (m + n) → Stack X n × Stack X m
split zero xs = xs ,, []
split (suc m) (xs , x) =
  let ys ,, zs = split m xs
  in  ys ,, zs , x

frame : ∀ {X m n k} → (Stack X m → Stack X n) → Stack X (m + k) → Stack X (n + k)
frame {m = m} f xs =
  let (ys ,, zs) = split m xs
  in  ys ++ (f zs)


framep : ∀ {X m n k}{P : Stack X m → Set} → ((s : Stack X m) → .(P s) → Stack X n) → (xs : Stack X (m + k)) → .(P (proj₂ $ split m xs)) → Stack X (n + k)
framep {m = m} f xs p =
  let (ys ,, zs) = split m xs
  in ys ++ (f zs p)


-- Framep is a version of frame that takes extra proof.
-- Now if we assume that framep is a fixed part of the 
-- interface and teach extractor how to deal with it.
iframep : ∀ {X m n k}{P : Stack X m → Set} 
        → ((s : Stack X m) → @0 (P s) → Stack X n) 
        → (xs : Stack X (m + k))
        → @0 (P (proj₂ $ split m xs))
        → Stack X (n + k)
iframep {m = m} f xs p =
  let (ys ,, zs) = split m xs
  in ys ++ (f zs p)

{-

module FibNonTerm where
  {-# TERMINATING #-}
  fib : ∀ {n} → Stack ℕ (1 + n) → Stack ℕ (1 + n)
  fib (xs , 0)             = xs , 1
  fib (xs , 1)             = xs , 1
  fib xs@(_ , suc (suc x)) = add $ fib $ sub $ push 2 $ exch $ fib $ sub $ push 1 $ dup xs



module FibWithSplit where
  fib′ : ∀ {y n} → (s : Stack ℕ (1 + n)) → (@0 _ : hd s < y) → Stack ℕ (1 + n)
  fib′ (xs , 0) _ = xs , 1
  fib′ (xs , 1) _ = xs , 1
  fib′ {suc y} xs@(l , r@(suc (suc x))) x<y =
    let
      l:r:r-1        = sub $ push 1 $ dup xs
      l:r ,, r-1     = split 1 l:r:r-1
      fib[r-1]       = fib′ r-1 (≤-pred x<y)
      l:r:fib[r-1]   = l:r ++ fib[r-1]
      -- XXX can we replace the three above lines with a `frame`-based call
      --     the problem is that when we do this we lose the information that
      --     (hd l:r:r-1) is (suc x).
      l:fib[r-1]:r-2 = sub $ push 2 $ exch l:r:fib[r-1]
    in                 add $ fib′ l:fib[r-1]:r-2
                                  (fib-thm {ys = fib[r-1]} (<-trans ≤-refl (≤-pred x<y)))
   where
    exch-++ : ∀ {X n}{xs : Stack X n}{ys : Stack X 1}{x} → exch ((xs , x) ++ ys) ≡ (xs ++ ys) , x
    exch-++ {ys = [] , y} = refl

    fib-thm : ∀ {n}{xs : Stack ℕ n}{ys : Stack ℕ 1}{x}{l} → x < l → hd (sub $ (exch ((xs , suc (suc x)) ++ ys) , 2)) < l
    fib-thm {ys = [] , y} x<l = x<l


  fib : ∀ {n} → Stack ℕ (1 + n) → Stack ℕ (1 + n)
  fib xs = fib′ xs ≤-refl

module WithSplitExtractFriendly where
  fib′ : ∀ {y n} → (s : Stack ℕ (1 + n)) → .(hd s < y) → Stack ℕ (1 + n)
  fib′ (xs , 0) _ = xs , 1
  fib′ (xs , 1) _ = xs , 1
  fib′ {suc y} xs@(l , r@(suc (suc x))) x<y =
    let
      l:r:r-1        = sub $ push 1 $ dup xs
                       -- Framep is a version of frame that takes extra proof.
                       -- Now if we assume that framep is a fixed part of the interface and teach extractor
                       -- how to deal with it.
      l:r:fib[r-1]   = framep {m = 1} {P = λ s → hd s ≡ suc x} (λ s hd[s]≡suc[x] → fib′ s (subst (_< y) (sym hd[s]≡suc[x]) (≤-pred x<y) )) l:r:r-1 refl
      l:fib[r-1]:r-2 = sub $ push 2 $ exch l:r:fib[r-1]
    in                 add $ fib′ l:fib[r-1]:r-2
                                  (fib-thm {ys =  fib′ ([] , suc x) _ } (<-trans ≤-refl (≤-pred x<y)))
   where
    exch-++ : ∀ {X n}{xs : Stack X n}{ys : Stack X 1}{x} → exch ((xs , x) ++ ys) ≡ (xs ++ ys) , x
    exch-++ {ys = [] , y} = refl

    fib-thm : ∀ {n}{xs : Stack ℕ n}{ys : Stack ℕ 1}{x}{l} → x < l → hd (sub $ (exch ((xs , suc (suc x)) ++ ys) , 2)) < l
    fib-thm {ys = [] , y} x<l = x<l


module IrrelWithSplitExtractFriendly where
  fib′ : ∀ {@0 y n} → (s : Stack ℕ (1 + n)) → @0 (hd s < y) → Stack ℕ (1 + n)
  fib′ (xs , 0) _ = xs , 1
  fib′ (xs , 1) _ = xs , 1
  fib′ {.suc y} xs@(l , r@(suc (suc x))) (s≤s x<y) =
    let
      l:r:r-1        = sub $ push 1 $ dup xs
      l:r:fib[r-1]   = iframep {m = 1} {P = λ s → suc x ≡ hd s}
                              (λ s hd[s]≡suc[x] → fib′ s (subst (_< y) hd[s]≡suc[x] x<y))
                              l:r:r-1 refl
      l:fib[r-1]:r-2 = sub $ push 2 $ exch l:r:fib[r-1]
    in                 add $ fib′ l:fib[r-1]:r-2
                                  (fib-thm {ys =  fib′ ([] , suc x) _ } (<-trans ≤-refl x<y))
   where
    fib-thm : ∀ {n}{xs : Stack ℕ n}{ys : Stack ℕ 1}{x}{l} 
            → x < l → hd (sub $ (exch ((xs , suc (suc x)) ++ ys) , 2)) < l
    fib-thm {ys = [] , y} x<l = x<l


module XIrrelWithSplitExtractFriendly where
  fib′ : ∀ {@0 y} → (s : Stack ℕ 1) → @0 (hd s < y) → Stack ℕ 1
  fib′ (xs , 0) _ = xs , 1
  fib′ (xs , 1) _ = xs , 1
  fib′ {.suc y} xs@(l , r@(suc (suc x))) (s≤s x<y) =
    let
      l:r:r-1        = sub $ push 1 $ dup xs

      l:r:fib[r-1]   = iframep {m = 1} {P = λ s → suc x ≡ hd s}
                              (λ s hd[s]≡suc[x] → fib′ s (subst (_< y) hd[s]≡suc[x] x<y))
                              l:r:r-1 refl
      l:fib[r-1]:r-2 = sub $ push 2 $ exch l:r:fib[r-1]

      l:fib[r-1]:fib[r-2] = iframep {m = 1} {P = λ s → x ≡ hd s}
                              (λ s x≡hd[s] → fib′ s (subst (_< y) x≡hd[s] (<-trans ≤-refl x<y)))
                              l:fib[r-1]:r-2 (exch-++ {ys = fib′ ([] , suc x) _})
    in add $ l:fib[r-1]:fib[r-2]
   where
    exch-++ : ∀ {n}{xs : Stack ℕ n}{ys : Stack ℕ 1}{x} 
            → x ≡ hd (proj₂ $ split 1 $ sub $ push 2 $ exch ((xs , suc (suc x)) ++ ys))
    exch-++ {ys = [] , y} = refl

  fib : ∀ {@0 n} → Stack ℕ (1 + n) → Stack ℕ (1 + n)
  --fib (xs , x) = xs ++ fib′ ([] , x) ≤-refl
  fib xs@(_ , _) = iframep {P = const ⊤ } (λ s _ → fib′ s ≤-refl) xs tt

module FibNoSplit where
  -- This is much more extraction-friendly version.
  -- It became much more complex due to the extra (irrelevant) proofs we carry around.
  -- XXX However, we still have the problem that we can't mark `y` as runtime-irrelevant.
  --     The only purpose of `y` is to sastisfy the termination checker, so we don't need
  --     it at runtime.  But I don't see how to mark it irrelevant or @0...

  infixl 3 _#_
  -- Stack with an irrelevant property
  record SProp (X : Set) (n : ℕ) (P : Stack X n → Set) : Set where
    constructor _#_
    field
      st : Stack X n
      .p : P st

  fib′ : ∀ {y n} → (s : Stack ℕ (1 + n)) → .(hd s < y) → SProp ℕ (1 + n) (λ s' → tl s' ≡ tl s)
  fib′ (xs , 0) _ = (xs , 1) # refl
  fib′ (xs , 1) _ = (xs , 1) # refl
  fib′ {suc y} xs@(l , r@(suc (suc x))) x<y =
     let
       l:r:r-1             = sub $ push 1 $ dup xs
       l:r:fib[r-1]        = fib′ l:r:r-1 (≤-pred x<y)
       l:fib[r-1]:r        : SProp ℕ _ λ s' → hd s' ≡ suc (suc x) × tl (tl s') ≡ l
       l:fib[r-1]:r        = (exch $ SProp.st l:r:fib[r-1])
                             #  (exch-hd {xs = SProp.st l:r:fib[r-1]} $ SProp.p l:r:fib[r-1])
                             ,, (exch-tl {xs = SProp.st l:r:fib[r-1]} $ SProp.p l:r:fib[r-1])
       l:fib[r-1]:r-2      : SProp ℕ _ λ s' → hd s' ≡ x × tl (tl s') ≡ l
       l:fib[r-1]:r-2      = (sub $ push 2 $ SProp.st l:fib[r-1]:r)
                             #  sub2-hd {xs = SProp.st l:fib[r-1]:r} (proj₁ $ SProp.p l:fib[r-1]:r)
                             ,, sub2-tl {xs = SProp.st l:fib[r-1]:r} (proj₂ $ SProp.p l:fib[r-1]:r)
       l:fib[r-1]:fib[r-2] = fib′ (SProp.st l:fib[r-1]:r-2)
                                  (subst (_< y) (sym $ proj₁ $ SProp.p l:fib[r-1]:r-2) (<-trans ≤-refl (≤-pred x<y)))
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


-}

