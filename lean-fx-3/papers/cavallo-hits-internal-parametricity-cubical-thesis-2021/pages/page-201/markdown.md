# Chapter 10

## Programming with parametricity

We now put our tools to the test and explore the consequences of internal parametricity. We start with a simple example to warm up in Section 10.1: a proof that the Church encoding of the booleans is isomorphic to the “primitive” boolean inductive type, which is a classical consequence of external parametricity [Wad07].

Next, in Section 10.2, we tackle a more theoretical result: the relativity principle, the equivalent of univalence for bridges, which states that bridges in U are isomorphic to relations. This result is novel: the principle is also true in Bernardy et al.’s calculus, but is ensured by imposing stricter equations on the equivalents of Gel types, while we do without them by leaning on function extensionality and univalence.

In Section 10.3, we identify the class of *bridge-discrete types*, those whose bridge types are isomorphic to their path types. We find that assumptions of bridge-discreteness play the role of classical parametricity’s *identity extension lemma*, which Nuyts et al. [NVD17] note is conspicuously absent from parametric type theory in the style of Bernardy, Coquand, and Moulin. We also show that the type of booleans is bridge-discrete, suggesting more generally how the bridge types of (higher) inductive types can be characterized. In Section 10.4, we note that this implies the refutation of a form of the excluded middle as a corollary.

Finally, we fulfill in Section 10.5 our promise of using internal parametricity to prove coherence results for the smash product.

### 10.1 Characterizing Church booleans

*Church encodings* are a method of obtaining inductive-like types through impredicative quantification, essentially defining an inductive type as the type of elements to which its recursion principle can be applied. As an example, consider the type of booleans, which we have as a primitive type as a particularly trivial consequence of Part II.

189