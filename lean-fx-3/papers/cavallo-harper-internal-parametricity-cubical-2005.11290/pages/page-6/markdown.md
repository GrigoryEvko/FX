5:6

E. CAVALLO AND R. HARPER

Vol. 17:4

We will indeed be able to use parametricity to characterize types of this form, showing that their only inhabitants are identity and constant functions.

**Internalizing parametricity.** Rather than constructing a model and showing that the denotations of terms satisfy parametricity properties, as Reynolds did, we follow Bernardy, Coquand, and Moulin's recent work [BM12, BM13, BCM15, Mou16] by *internalizing* parametricity as part of our type theory. Bernardy and Moulin introduce so-called *parametricity primitives*, new type and term formers that make it possible to prove theorems such as the following.

$$(f:(A\mathcal{U}) \to A \to A) (A\mathcal{U}) (a:A) \to \mathsf{Id}_A(fAa, a)$$

Notably, these primitives have a computational interpretation. We take the ideas of internal parametricity and apply them to contentful equality, producing a *parametric cubical type theory*.

Internalizing parametricity has the advantage of allowing us to use parametricity results without going outside the theory. It is, moreover, coherent with the perspective that leads us to the univalence axiom. From one angle, univalence serves to internalize the action of type-theoretic constructions on isomorphisms. In much the same way, internal parametricity expresses the action of constructions on relations. We are not the first to remark on the similarity between the two—both Atkey *et al.* and Bernardy *et al.* make the observation—but we will endeavor here to sharpen the comparison. Parametric type theory bears a strong resemblance to cubical type theory, particularly as presented by Bernardy, Coquand, and Moulin (BCM) [BCM15]. We will explore that resemblance here, with special attention to the points at which cubical and parametric type theory diverge.

**Contributions.** Our results can be divided into several camps, depending on how they relate to the interplay between internal parametricity and cubical equality.

First, we establish that parametricity primitives can in fact be added to cubical type theory. Our combined type theory is grounded in a computational interpretation in the style of Allen [All87], following the work of Angiuli *et al.* for cubical type theory [AFH18]. Starting from the computational interpretation, we abstract a formal, generalized algebraic type theory. We show that this theory also has interpretation in (some variety of) Kan bicubical sets. In all these constructions, the cubical side is already fairly well understood, so we focus on the parametricity primitives.

Next, we come to applications. On the one hand, we use internal parametricity as a tool for proving theorems in cubical type theory. Here, the smash product is our representative example of a higher inductive type with complex algebraic structure. We show that in internally parametric type theory, we can obtain the higher coherence properties of the smash product in a uniform way. While the proofs are still not trivial, they are distinguished from the prior work by their scalability: it is not much more difficult to obtain $n$-coherent structure than 1-coherent structure.

On the other hand, we use the well-behaved equality of cubical type theory to regularize parametric type theory. Just as cubical equality produces an extensionality principle for function types, it implies extensionality principles for the parametricity primitives. In the presence of univalence, we can also make do with a weaker version of Gel-types, the other parametricity primitive, than is used in the BCM theory. This allows us to give a simpler