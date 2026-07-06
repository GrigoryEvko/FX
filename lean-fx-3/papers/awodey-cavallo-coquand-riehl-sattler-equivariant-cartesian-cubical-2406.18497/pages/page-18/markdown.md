For instance, for any object $X \in \mathsf{E}$, such an adjunction is given by the pullback functor along $X \to 1$:

$$\mathsf{E}_{/X} \xrightarrow[\perp]{X^*} \mathsf{E}.$$

Thus a locally representable notion of fibred structure on $\mathsf{E}$ may be lifted to its slice categories.

2.2. Monomorphisms and uniform trivial fibrations. Let $\mathsf{E}$ be an elementary topos and write $\top: 1 \to \Omega$ for its subobject classifier. We consider a class of “trivial fibrations” characterized by the right lifting property against the monomorphisms and show that it underlies a notion of fibred structure which we call uniform trivial fibration structure. We then show that this notion of fibred structure is locally representable.

First, since elementary toposes are in particular locally cartesian closed, every map $f: X \to Y$ in $\mathsf{E}$ induces an adjoint triple of functors

$$\mathsf{E}_{/X} \xleftarrow[\perp]{f^*} \mathsf{E}_{/Y}$$

where $f_!$ is post-composition, $f^*$ is pullback, and $f_*$ is (by definition) pushforward. Furthermore, the following applies to $\mathsf{E}$:

Lemma 2.2.1. In a locally cartesian closed category, the pullback-pushforward adjunction $i^* \dashv i_*$ along a monomorphism $i$ forms a reflective embedding.

Proof. The counit of $i^* \dashv i_*$ is an isomorphism just when its conjugate, the unit of $i_! \dashv i^*$, is an isomorphism, but the latter is clear, since the pullback of $i$ along itself is an isomorphism. □

We note the following closure property of monomorphisms in a topos, for later use:

Remark 2.2.2. Since elementary toposes are adhesive, the class of monomorphisms is closed under pushout products, and the same is true in slice categories: given a pair of monomorphisms $i: A \mapsto B$ and $j: C \mapsto D$, the pushout product is the join of the subobjects $i \times D: A \times D \mapsto B \times D$ and $B \times j: B \times C \mapsto B \times D$ [LS04, 17].

We now use the subobject classifier to define partial map classifiers (called partial-map representers in [PTJ02, §A.2.4]). In turn, these will be used to define our trivial fibrations. The following two propositions are proven in [Awo26, §3] (see also [PTJ02, A2.4.7] and [GS17, 9.8–9]):

Proposition 2.2.3. For any $Y \in \mathsf{E}$, there is a pullback square as below-left with the property that any partial map as below-right

$$\begin{array}{ccc} Y & \xrightarrow{!} & 1 \\ \eta_Y \downarrow & \downarrow^\top & \downarrow^\top \\ Y^+ & \xrightarrow{\top_* Y} & \Omega \end{array} \qquad \begin{array}{c} C & \xrightarrow{y} & Y \\ \downarrow^c & \\ Z & \end{array}$$

18