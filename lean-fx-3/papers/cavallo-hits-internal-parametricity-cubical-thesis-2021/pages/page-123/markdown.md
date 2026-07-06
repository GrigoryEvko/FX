# Chapter 6

## General higher inductive types

We now assemble the strategies used for the examples in Chapter 5 into a general schema for higher inductive types and a computational interpretation for the instances thereof.

We begin in Section 6.1 by defining a specification schema: a formal language making precise the pseudo-code “**inductive**” declarations we have used thus far. The specification of a higher inductive type involves both types (the types of arguments to constructors) and terms (the boundaries of constructors), and so the specification language itself has the structure of a formal type theory, restricted so that its instances describe monotone operators on indexed relations.

In Section 6.2, we define an interpretation of this formal type theory into the underlying computational type theory. We use the interpretation to define the monotone operator on relations corresponding to an inductive specification. The relation for the inductive type in question is then defined as the least fixed-point of said operator. Using this definition on the level of relations, we construct a type system closed under indexed higher inductive pretypes. In the process, we show that the inductive relations are value-coherent, which amounts to proving the introduction rules for each constructor and for formal composition and coercion terms.

Next, in Section 6.3, we establish that the higher inductive pretypes support the Kan operations, making them full-fledged types. We easily dispense with composition, having already shown that the inductive type is closed under formal compositions. Defining and checking the well-typedness of coercion is much more involved. The definition requires a combination of the techniques used to handle path constructors (Section 5.1) and indices (Section 5.3) above. The proof of well-typedness, meanwhile, requires careful staging to manage the recursive structure of inductive types, stemming both from recursive constructors and the recursive formal Kan operators.

We complete the picture in Section 6.4 by establishing elimination principles for our higher inductive types. This again proceeds in several stages: defining the data required to eliminate from a given inductive type, defining the operational semantics of an elimina-

111