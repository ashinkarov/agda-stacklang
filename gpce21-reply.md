We thank the reviewers for their honest and insightful comments. We
wish to start by reiterating two important points.

First, the example DSL in the paper is perhaps not
the most practical to use. However, our main goal was never to show
the usability of this particular embedded language, but rather the
feasibility of defining the embedding, its correctness properties, and
the extractor for it side-by-side in the same host language.

Secondly, our choice to start from a shallow embedding instead of a
deep one is not just because of convenience in the definition of the
embedding. If we want to capture non-trivial properties of programs,
the deep embedding requires us to implement a separate typechecker
(for dependent types!), while with a shallow embedding we can simply
reuse the typechecker of the host language.

In the remainder of this response, we go into more detail on each of
the individual comments.


> GPCE 2021 Paper #18 Reviews and Comments
> ===========================================================================
> Paper #18 Extracting The Power of Dependent Types
> 
> 
> Review #18A
> ===========================================================================
> 
> Overall merit
> -------------
> 4. Accept
> 
> Reviewer expertise
> ------------------
> 4. Expert
> 
> Paper summary
> -------------
> This paper presents a technique for embedding languages in Agda in such a way
> that properties of programs in the embedded language can be tracked in the Agda
> type system while at the same time supporting a code extraction mechanism. The
> main example is Postscript and preserving stack invariants.
> 
> Comments for author
> -------------------
> This is a nice paper on how to embed languages in Agda. It is relatively easy
> to understand when one has something basic familiarity with Agda. If one does
> not, then I guess it would be considerably harder.
> 
> While I do like the approach, I also think the paper could be more open about
> the downsides of their approach:
> 
> * The way the language is embedded would make it hard to port existing code
>   (such as existing Postscript code) into this framework. There are various
>   differences, and they are not merely of a syntactical nature. For instance,
>   conditionals are expressed in a different way. For-loops are expressed
>   differently and are more restrictive. It is in general not clear how much
>   work it would be to port existing code and to which degree this is even
>   possible.

You are right, these are interesting questions indeed.  However, we never claimed
that it would be possible to literally port existing programs into the proposed
system.  Our main point is to demonstrate that you can add arbitrary properties
to the programs that you will execute in the chosen language.  As we are pursuing an
intrinsic approach, where proofs are parts of programs, it would be hard to imagine
that there exists an approach that makes it possible to automatically port any
existing programs into the proposed system with strong invariants, since in general
there is no way to infer the invariants automatically.

> * I think the main downside of the approach is that there is no enforcement
>   that the embedded programs actually correspond to Postscript programs. They
>   can consist of arbitrary Agda code. If the programmer uses something that is
>   not explicitly supported, the code extraction will simply fail.

The proposed technology allows one to programmatically add such an enforcement
before attempting the extraction.  We have chosen not to do so, as this allows for
functions in the host language to be used as macros (as demonstrated in section 5
of the paper).  However, this is not a limitation of the proposed system.

> * It is claimed that the embedding approach works for dependently typed host
>   languages such as Coq, Agda, Idris or Lean. Do all these languages support
>   reflection in such a way to make your code extraction approach work?

All of these systems support reflection in a similar way to Agda, and nothing in
the documentation of these systems suggests our approach would not work.
Since we have not actually tried it, there is surely a chance that some feature
of the reflection machinery does not work as advertised.
However, that is likely to be a technical problem/bug rather
than a fundamental restriction.  Fundamentally, there is nothing special about
Agda that can't be recreated in the systems mentioned.

> Some more detailed comments:
> 
> I'm not sure I buy the claim about the difficulty of a deep embedding for the
> particular example in the paper. Dependent types are only used in a very
> limited way. The main benefit of using a deep embedding, compared to your
> approach, would be that one would have a model of well-defined embedded
> language programs. I would have appreciated if the authors would have at least
> given deep embedding a chance and not reject it possibly prematurely.

You are right, for the particular example in the paper, our approach might be overkill.
However, our main point was to demonstrate the technology, and postscript is
a simple enough example where dependent types are needed to express properties,
e.g. the `rep` function.  We are not claiming that embedding postscript this way is
very practical, but we did demonstrate our technology.  We tried explaining this
in paragraph at line 136, which we are happy to improve.  As for deep embedding,
we simply ran out of space.  There is plenty of things we could say, but we chose
the main focus to be around the extraction technology.

> l. 321, what is the T in TC_T? Is that an application of the TC type
> constructor to the unit type? Then why is it typeset as an index?

This is not TC_T, but TC \top, where \top is the unicode symbol.  This is not
an index, we can make a footnote in the text to clarify this.

> l. 500 couldn't you modify |> in such a way that one could write in a fully
> point-free style, i.e.
> 
> add-1 = push 1 |> add 
>
> ?

Yes, one could surely do this.  Our motivation for not doing this is that we
sometimes want to pass the argument explicitly, and in this case we would have
to introduce two operations "|>" and reverse composition for point-free expressions.
We have chosen to minimise the number of additional constructions and be explicit.

> l. 519-526: don't you get further and further away from the original PS syntax?
> Wouldn't I want to basically copy&paste existing PS into your machinery? What
> is the complete set of things I have to do to port existing PS code into your
> flat embedding?

The problem with porting PS programs "as is" is that you'd have to convince Agda
that these programs adhere to invariants that you have put in the types.  It is
easy to specify all the PS commands as they are, but it might be quite inconvenient
to work with them.  Potentially one could end up wrapping a lot of commands with
"subst"s that propagate stack invariants.  By making the structure of the code
more explicit, Agda can deduce many things automatically.

> l. 586-594 : I don't know how to read that code. Line by line? Left column,
> then right column? What does the checkmark mean?

Two columns; checkmark is the name of the function.  We'll make this explicit in
the text.

> 
> 
> 
> Review #18B
> ===========================================================================
> 
> Overall merit
> -------------
> 1. Reject
> 
> Reviewer expertise
> ------------------
> 3. Knowledgeable
> 
> Paper summary
> -------------
> The paper proposes a methodology to embed a DSL into a dependently typed host
> language. The methodology is illustrated by an example (embedding a subset of
> PostScript into Agda). The aim is to be able to prove (in Agda) program
> properties.  The methodology, explained on the example, works as follows: 
> 
> (1) A shallow embedding of the Postscript subset into Agda is defined.  A
> program in this DSL is a list of commands. The semantics of a command is a
> function from stacks of integers into stacks of integers (for instance, the
> "add" command transforms the stack a b s into the stack a+b s). "Shallow
> embedding" means that we can write an Agda type for stacks (indexed on the
> length), and Agda functions corresponding to commands. Thanks to the Agda type
> system it is possible to express constraints (e.g., that "add" has type
> Stack(n+2) -> Stack(n+1)), and, more in general, to prove properties of
> programs. 
> 
> (2) The second step uses Agda reflection. Agda terms can be internally
> represented by elements of a datatype Term. Then, an "extractor" is defined
> which (roughly), given an Agda (reflected) term, returns (if possible) a
> Postscript program. The authors claim that the advantage is that in this way
> the obtained Postscript program is "correct by construction", since we have
> formally proved the properties of its Agda version.
> 
> Comments for author
> -------------------
> Maybe I am missing something, but I am not able to see the advantages of the
> approach. A "shallow embedding" basically maps DSL types/expressions into
> types/expressions of the host language.  The fact that if the host language is,
> e.g., Agda, you can prove properties of the translated programs, is obvious. On
> the other hand, the fact that you go the other way round, by mapping
> types/expressions of the host language into DSL types/expressions, seems very
> counterintuitive.  Do you mean that to write a correct PostScript program one
> should start from developing its equivalent Agda function and then get the
> extracted program?

Yes, it is mentioned in line 128, item (i).  However, this is not an arbitrary Agda
function, but rather an Agda function that is composed of the basic postscript operators
embedded in Agda.  Notice that our entire PS embedding is ~20 lines of Agda.
Typically, one would have to define a type that would capture most of the invariants
(Stack in our case) and a small number of base operators.  As most of the basic
concepts such as variables, functions, conditionals are present in Agda, we do
not add those separately to the embedding.  We are reusing them.

> I think that programmers would like to write DSL programs
> and to have tools (in a more powerful language) to prove they to be correct.

The key question is: what does "correct" mean here?  DSLs like PostScript do
not have a type system, so the first problem is to *be able* to specify the
properties about programs.  That is what dependent types are good for, and that
what this entire paper is all about.  As types must annotate some
terms, there needs to be some DSL embedding.  You can vary the level
of the information that your embedded terms carry.  This difference is often referred as
extrinsic vs intrinsic verification.  The former separates the property you want
to observe from the embedding, the latter interleaves them.  The literature does
not give a clear answer of choosing one over the other. The extrinsic approach often
comes with large proofs that are difficult to work with, especially for properties that
require dependent types to express.  In the intrinsic approach
the proofs are interleaved with the code, but in systems like Agda you get a lot
of automation and much simpler proofs.  This paper advocates the intrinsic approach.


> This can be easily done by the "standard" approach (deep embedding) of
> implementing in Agda bot the DSL syntax and semantics (in practice,
> implementing an intepreter).

Unfortunately, this is not that easy at all.  Defining a syntax and semantics
of the PostScript is surely easy.  However, PostScript is untyped.  Therefore,
in order to state (interesting!) properties about PS programs, you would have to
implement a custom typechecker that can handle dependent types.  This work says
that we can instead share the typecheker of the host language.

> I know that this can lead to some overhead, but is very clear and supports
> modular change of semantics.

This is about more than just overhead, implementing a custom dependent typechecker
is far from trivial.  Also, as there is no way to infer an arbitrary property
about the embedded program (because the type may depend on arbitrary computations),
some manual proofs will be required anyway.

I am not sure what is meant by "modular change of semantics".  In the current
embedding you can also change the semantics of the base operators.  It will have
consequences on the programs.  But the same consequences would happen in the
extrinsic case.

> Another important criticism is that I do not see how to lift your example to a
> general construction, working for a given class of DSLs. 

As we say in conclusions, line 1296, in this paper https://arxiv.org/abs/2105.10819
it is demonstrated how a similar approach can be lifted into a small framework
where we give examples for three non-trivial DSLs.

> 
> Small comments and typos
> 
> 166 to our -> our
> 
> 234 you are using here 1,2, but you only introduced zero and suc until now

You are right, we should mention that this refers to the same thing.
> 
> 321 Functions of return type -> Functions of type   (I guess?)
> 
> 336 for both, -> for both
> 
> 458 what is T here?

This is a function that turns a boolean values to types (false becomes the
empty type, and true becomes the unit type).  We are happy to mention this in
the text.

> 
> 
> 
> Review #18C
> ===========================================================================
> 
> Overall merit
> -------------
> 5. Strong accept
> 
> Reviewer expertise
> ------------------
> 3. Knowledgeable
> 
> Paper summary
> -------------
> This paper presents an effective method to embed an (object) programming
> language in a dependently typed language, so that one can reason about
> properties of programs written in the object language, and also can manipulate
> abstract syntax trees for them, thus allowing to write, for instance, a
> compiler and a partial evaluator for the object language. The key trick is to
> use a dependently typed language with the reflection mechanism.  The paper
> demonstrates how this idea works in practice, by embedding a PostScript-like
> language in Agda and also shows how program extraction and partial evaluation
> can be done in this framework.
> 
> Comments for author
> -------------------
> Evaluation
> 
> This is really an interesting paper; it presents a way to specify&reason about
> programs’ properties where the object programming language does not have a
> sufficiently strong type system such as dependent types. A naïve way is to
> embed the object language in a richer language for logical reasoning, but both
> shallow embedding and deep embedding have some certain drawbacks, which makes
> it difficult to achieve the goal with little cost. The novel approach proposed
> in this paper is to take advantage of reflection in the host language, which
> allows one to manipulate AST of (the normal forms of) the programs in the
> object language, thus one can compile a shallowly embedded program, or
> partially evaluate it. The idea is interesting in its own right, but the
> strength of this paper is to demonstrate how all the processes are actually
> done for non-trivial object language and Agda as the host language. I really
> enjoyed in reading the development in this paper, which provides sufficient
> explanation for non-expert readers.  Therefore, I am strongly in favor of this
> paper.
> 
> Other comments
> 
> -　Although I appreciate the idea, methodology, implementation of this paper
> very much, an (obvious) concern is the lack of correctness guarantee of a code
> extractor (a compiler) as the paper itself mentions in the conclusion section.
> Obviously, if the extracted code has different semantics than the program
> before extraction, then any verification on the latter makes no sense for the
> former, which may completely destroy the merits of this approach. I think the
> paper does not have a big problem since it makes this fact explicit. However,
> the abstract of this paper mentions ‘correct-by-construction’, and several
> places in the paper mentions ‘verification’ of (object) programs, which is (in
> my view) misleading, hence I encourage the author to clarify what is meant by
> ‘correct’/’verify’ in an early part of this paper (e.g. in Section 1).

We are happy to clarify this in the revised text.

> -　The paper reveals the fact that, even using this paper’s brilliant idea, it
> is rather difficult to fully carry out the embedding and program extraction for
> non-trivial object language. One needs to understand how Agda’s quoted
> terms/types are structured (which is quite puzzling for non-experts) etc., so
> writing any programs is quite non-trivial.  I wonder if there is a more
> systematic treatment for the implementation part.

In https://arxiv.org/abs/2105.10819 we build a small framework for
defining embedded DSLs and extractors and implement three DSLs in it.
While the core part would always have to deal with the reflected
syntax, this shows that a number of mechanisms can be generalised.

> -　Oleg Kiselyov and others' ‘tagless-final’ embedding might be relevant to
> this work, since it can be used to shallowly embed object languages, but can
> work as a compiler by choosing an appropriate interpretation.  Although they
> have used it for non-dependently typed domain-specific languages only, one can
> easily imagine its application to, say, Coq, since it has modules. I am not
> sure if such a combination works in practice, but you had better mention it in
> the revised version of this paper.

As we mention in lines 98-99, tagless embeddings for dependently-typed DSLs are
perfectly possible, unfortunately it is very impractical to write programs in them.
For example, "Outrageous but meaningful coincidences: dependent type-safe syntax
and evaluation" by Conor McBride shows very clearly why this is the case.
As for Coq modules, it is unclear how this could solve the problem of the mix
of specification and encoding that happens in the dependently-typed tagless
embeddings.

>       Carette, Kiselov, Shan, “Finally tagless, partially evaluated: Tagless
>       staged interpreters for simpler typed languages”, JFP Vol. 19, 2009.

We are happy to reference this paper as well.

> 
> Minor points
> -	Ocaml and MetaOcaml should be OCaml and MetaOCaml (capital ‘C’).

Yes, you are correct, we will fix that.

> -	Line 531: what is the check mark after ‘proof’?

This is the name of the proof (function), we will make this explicit in the text.

> -	Line 540: ‘a dependency’ -> ‘dependency’
> 
