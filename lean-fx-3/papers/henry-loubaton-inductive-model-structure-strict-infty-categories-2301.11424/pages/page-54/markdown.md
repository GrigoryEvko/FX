We will use the join to define the adjunction between stratified simplicial sets and marked $\infty$-categories.

**4.50 Definition.** Let $(C, M)$ and $(D, N)$ be two marked $\infty$-categories. The *join* of $(C, M)$ and $(D, N)$, denoted $(C, M) \star (D, N)$, is the colimit of the following diagram:

$$\begin{array}{ccc} C \ominus \{0\} \ominus D & \coprod C \ominus \{1\} \ominus D & \longrightarrow & C \ominus \mathbb{D}_1 \ominus D \\ \downarrow & & \downarrow \\ C \coprod B & & \longrightarrow & C \star B \end{array}$$

As noted in Proposition 3.3.11 of [3] at the level of $\infty$-categories, this is the usual join of $\infty$-categories, as defined in Paragraph 6.30 of [6]. By the definition of the operation $\ominus$, we then have $(C, M) \star (D, N) \cong (C \star D, \overline{M \star N})$, where

$$M \star N := \{x \star y \mid x \in M, y \in N\} \cup \{x \star \emptyset \mid x \in M\} \cup \{\emptyset \star y \mid y \in N\}.$$

**4.51 Proposition.** Let $X \rightarrow Y$ be a *cofibration* and $K \rightarrow L$ an *acyclic cofibration* of $\infty$-Cat$^{+\infty}_{Sat-Ind}$. The morphisms

$$K \star Y \coprod_{X \star K} L \star X \rightarrow L \star Y \quad \text{and} \quad Y \star K \coprod_{K \star X} X \star L \rightarrow Y \star L$$

are *acyclic cofibrations* of $\infty$-Cat$^{+\infty}_{Sat-Ind}$.

*Proof.* By construction, we have a cocartesian square

$$\begin{array}{ccc} K \ominus \mathbb{D}_1 \ominus Y \cup L \ominus \partial \mathbb{D}_1 \ominus Y \cup L \ominus \mathbb{D}_1 \ominus X & \longrightarrow & K \star Y \coprod_{X \star K} L \star X \\ \downarrow & & \downarrow \\ L \ominus \mathbb{D}_1 \ominus Y & & \longmapsto & L \star Y \end{array}$$

By Lemma 2.42, the left-hand vertical morphism is an acyclic cofibration, and so is the right one. We proceed analogously for the second morphism. $\square$

**4.52 Definition.** The terminal category 1 has a monoid structure for this join operation. The multiplication $1 \star 1 \rightarrow 1$ is the unique morphism to the terminal $\infty$-category.

By the universal property of the category $\Delta$, this induces a cosimplicial object $|-|: \Delta \rightarrow \infty$-Cat$^{+\infty}$ where

$$|\Delta[n]| := 1 \star 1 \star \dots \star 1.$$

The $\omega$-category $|\Delta[n]|$ is traditionally called the $n^{th}$ oriental. We denote $|-|: \mathbf{Sset} \rightarrow \infty$-Cat$^{+\infty}$ the extension by colimits of this cosimplicial object.

For all $n$, $|\Delta[n]|$ is an $n$-polygraph that admits only one $n$-generator. If $M$ is a marking for $K$, we denote $|M|$ the set of arrows obtained as composition:

$$\mathbb{D}_n \rightarrow \Delta[n] \xrightarrow{|v|} K$$

54