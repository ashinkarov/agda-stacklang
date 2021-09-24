Extracting the Power of Dependent Types
=======================================

This repository hosts the sources of the paper
"Extracting The Power of Dependent Types" by
Artjoms Sinkarovs and Jesper Cockx.

Key idea
--------

In this paper we demonstrate a technique on enriching
your language with dependent types by first embedding it
in Agda and then extracting the programs into the original
language so that existing tools could be used.
Within the shallow embedding full power of dependent types
can be used to prove properties about programs.  Translation
from the shallow embedding is the main novelty of the approach.
It is based on Agda's reflection capabilities, so it becomes
possible to express simultaneously:

 * shallow embedding;
 * programs in the embedding; and
 * compiler from the embedding into the original language.

The paper focuses on demonstrating basic ingredients of the
technique.  Therefore, we have consciously chosen a minimalist
language that lets us express programs that require dependencies
between the values and the invariants we are observing.
Our example language is PostScript, and our invariant is the
stack length.

Examples
========

As an example, consider the following embedded program, its extracted
version and postscript-generated picture.


<table>
<tr>
    <td>Embedding </td>
    <td>Extraction</td>
</tr>
<tr>
  <td>

```agda
-- Two external functions that we are not specifying here      
draw-circ-xy : Stack (2 + n) → Stack n
bit-and : Stack (2 + n) → Stack (1 + n)      
      
draw-if : Stack (3 + n) → Stack (2 + n)
draw-if s@(_ # 0) = s  ▹ pop ▹ index 1 
                       ▹ index 1 ▹ draw-circ-xy
draw-if s         = s  ▹ pop
      
sierpinski : Stack (1 + n) → Stack n
sierpinski s  =
  s ▹ push 0 ▹ index 1
    ▹ for (λ s → s ▹ push 0 ▹ index 2
                   ▹ for (λ s → s ▹ index 1 ▹ index 1
                                  ▹ bit-and ▹ draw-if ▹ pop)
                   ▹ pop)
    ▹ pop
```    
  </td>
  <td>

```ps
/draw-if {
  0 index 0 eq {
    pop 1 index 1 index draw-circ-xy
  }{
    pop
  } ifelse
} def
      
/sierpinski {
  0 1 index 
  1 exch {
    0 2 index 
    1 exch {
      1 index 1 index 
      bit-and draw-if pop
    } for pop
  } for pop
} def
```

  </td>
  </tr>
</table>

Feeding the code on the right (providing the definitions of `bit-and` and `draw-circ-xy`)
into a PostScript interpreter produces the following image.

<p align="center">
  <img height="20%" width="20%" src="sierp.png" />
</p>

A slightly more interesting example is a function `rep` that takes two
arguments `x` and `n` and repeats (copies) `x` `n` times.  How can you
guarantee that the function behaves according to the specification?
In the proposed system dependent types come to rescue.

<table>
<tr>
    <td>Embedding </td>
    <td>Extraction</td>
</tr>    
<tr>
  <td>

```agda
rep′ : (s : Stack (2 + n)) → @0 (s ! 0 ≡ k) → Stack ((s ! 0) + n)
rep′ s@(_ # zero)   refl  = s ▹ pop ▹ pop
rep′ s@(_ # suc m)  refl  =
     let s′ = s ▹ push 1 ▹ sub ▹ index 1 ▹ exch
     in  subst-stack (+-suc _ _) (rep′ {k = m} s′ refl)

rep : (s : Stack (2 + n)) → Stack ((s ! 0) + n)
rep s = rep′ s refl
```    
  </td>
  <td>

```ps
/rep′ {
  0 index 0 eq {
    pop pop
  } {
    1 sub 1 index exch rep′
  } ifelse
} def

/rep { rep′ } def
```

  </td>
  </tr>
</table>

While this may look a bit ugly, there is a lot of things going on.  Firstly, we
are **able** to specify that the length of the resulting stack increased by the
number of elements that corresponds to the top position of the input stack `s ! 0`
and decreasd by two elements.  Secondly, it is **guaranteed** that this (recursive)
function is terminating.  This is the reason why we have `rep′` and `rep`.  However,
in the extraction all the complexity is eliminated.

For more examples, read the paper or have a look at `psembedding.lagda` and `extraction.lagda`
files.  The latter containns various extraction test cases, pretty much for every examples used
in the paper.

Extras
======

### Partial evaluation via inlining

By controlling how much basic operators are allowed
to be inlined, we can partially evaluate our programs:

<table>
<tr>
    <td>Embedding </td>
    <td>Extraction</td>
</tr>    
<tr>
  <td>

```agda
-- Loop unrolling
sum : Stack (1 + n) → Stack (1 + n)
sum s = for add (s ▹ push 0 ▹ exch ▹ push 0 ▹ exch)

-- Use the above sum definition
ex : Stack n → Stack (1 + n)
ex s = sum (s ▹ push 4)

-- Extract with: extract ex (quote add ∷ [])      
```    
  </td>
  <td>

```ps
% Loop unrolled
/ex {
  0 0 add 1 add 2 add 3 add 4 add
} def
```

  </td>
  </tr>
</table>



### Domain-specific optimisations via rewrite rules.

By proving the following lemma about push-add-push-add pattern:

```agda
add-add-join : (s : Stack (1 + n)) (k l : ℕ)
  → s ▹ push k ▹ add ▹ push l ▹ add ≡ s ▹ push (k + l) ▹ add
add-add-join (s # x) k l = cong (s #_) (+-assoc x k l)
```
and registering it as a rewrite rule
```agda
{-# REWRITE add-add-join #-}
```

Our extraction can do the following:

<table>
<tr>
    <td>Embedding </td>
    <td>Extraction</td>
</tr>    
<tr>
  <td>

```agda
add-some-numbers : Stack (1 + n) → Stack (1 + n)
add-some-numbers s = s  ▹ push 1 ▹ add  ▹ push 2 ▹ add
                        ▹ push 4 ▹ add  ▹ push 2 ▹ add
```    
  </td>
  <td>

```ps
% Without the rewrite rule
/add-some-numbers { 1 add 2 add 4 add 2 add } def
% With the rule
/add-some-numbers { 9 add } def
```

  </td>
  </tr>
</table>

Note that the original code does not reduce as we know nothing about the
top element of the input stack.  Reshuffling of additions requires more than
simple function inlining.

