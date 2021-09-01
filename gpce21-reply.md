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
to the programs that you will execute in the chosen language.  As we are pursuing
intrinsic approach, where proofs are parts of programs, it would be hard to imagine
that there exists an approach that makes it possible to automatically port any
existing programs into the proposed system with strong invariants.  The invariants
would have to come from somewhere.

> * I think the main downside of the approach is that there is no enforcement
>   that the embedded programs actually correspond to Postscript programs. They
>   can consist of arbitrary Agda code. If the programmer uses something that is
>   not explicitly supported, the code extraction will simply fail.

The proposed technology allows one to programmatically add such an enforcement
before attempting the extraction.  We have chosen not to do so, as the proposed
"macros" may be useful.  However, this does not seem to be the limitation of the
proposed system.

> * It is claimed that the embedding approach works for dependently typed host
>   languages such as Coq, Agda, Idris or Lean. Do all these languages support
>   reflection in such a way to make your code extraction approach work?

According to the documentation available to us that seem to be the case.
There is surely a chance that some feature of the reflection machinery does not
work as advertised.  However, that is likely to be a technical problem/bug rather
than a fundamental restriction.  Fundamentally, there is nothing special about
Agda that can't be recreated in the systems you mention.

> Some more detailed comments:
> 
> I'm not sure I buy the claim about the difficulty of a deep embedding for the
> particular example in the paper. Dependent types are only used in a very
> limited way. The main benefit of using a deep embedding, compared to your
> approach, would be that one would have a model of well-defined embedded
> language programs. I would have appreciated if the authors would have at least
> given deep embedding a chance and not reject it possibly prematurely.

You are right, for a particular postscript example, this might be an overkill.
However, our main point was to demonstrate the technology, and postscript is
a simple enough example where you can create precedents for using dependent types,
i.e. rep function.  We are not claiming that embedding postscript this way is
very practical, but we did demonstrate our technology.  We tried explaining this
in paragraph at line 136, which we are happy to improve.  As for deep embedding,
we simply ran out of space.  There is plenty of things we could say, but we chose
the main focus to be around the extraction technology.

> l. 321, what is the T in TC_T? Is that an application of the TC type
> constructor to the unit type? Then why is it typeset as an index?

This is not TC_T, this TC \top, where \top is the unicode symbol.  This is not
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
to work with them.  Potentially one could end-up wrapping a lot of commands with
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
> extracted program? I think that programmers would like to write DSL programs
> and to have tools (in a more powerful language) to prove they to be correct.
> This can be easily done by the "standard" approach (deep embedding) of
> implementing in Agda bot the DSL syntax and semantics (in practice,
> implementing an intepreter). I know that this can lead to some overhead, but is
> very clear and supports modular change of semantics.
> 
> Another important criticism is that I do not see how to lift your example to a
> general construction, working for a given class of DSLs. 
> 
> Small comments and typos
> 
> 166 to our -> our
> 
> 234 you are using here 1,2, but you only introduced zero and suc until now
> 
> 321 Functions of return type -> Functions of type   (I guess?)
> 
> 336 for both, -> for both
> 
> 458 what is T here?
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
> 
> -　The paper reveals the fact that, even using this paper’s brilliant idea, it
> is rather difficult to fully carry out the embedding and program extraction for
> non-trivial object language. One needs to understand how Agda’s quoted
> terms/types are structured (which is quite puzzling for non-experts) etc., so
> writing any programs is quite non-trivial.  I wonder if there is a more
> systematic treatment for the implementation part.
> 
> -　Oleg Kiselyov and others' ‘tagless-final’ embedding might be relevant to
> this work, since it can be used to shallowly embed object languages, but can
> work as a compiler by choosing an appropriate interpretation.  Although they
> have used it for non-dependently typed domain-specific languages only, one can
> easily imagine its application to, say, Coq, since it has modules. I am not
> sure if such a combination works in practice, but you had better mention it in
> the revised version of this paper.
>       Carette, Kiselov, Shan, “Finally tagless, partially evaluated: Tagless
>       staged interpreters for simpler typed languages”, JFP Vol. 19, 2009.
> 
> Minor points
> -	Ocaml and MetaOcaml should be OCaml and MetaOCaml (capital ‘C’).
> -	Line 531: what is the check mark after ‘proof’?
> -	Line 540: ‘a dependency’ -> ‘dependency’
> 
