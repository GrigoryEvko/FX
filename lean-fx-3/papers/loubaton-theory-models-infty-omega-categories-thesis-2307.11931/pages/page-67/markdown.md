1.2. GRAY OPERATIONS

**1.2.3.12.** The following propositions express the link between the Gray operations and the suspension. They will play a fundamental role in the rest of this work.

**Theorem 1.2.3.13.** *Let $C$ be an $(0, \omega)$-category. There is a natural identification between $[C, 1] \otimes [1]$ and the colimit of the following diagram*

$$[1] \vee [C, 1] \longleftarrow [C \otimes \{0\}, 1] \longrightarrow [C \otimes [1], 1] \longleftarrow [C \otimes \{1\}, 1] \longrightarrow [C, 1] \vee [1]$$

*Proof.* As all these functors preserve colimits, it is sufficient to construct the comparison when $C$ is a globular sum, and to show that it is an equivalence when $C$ is a globe. As globular sums have atomic and loop free bases, the comparison is induced by proposition 1.2.2.17. Using the explicit description of the $(0, \omega)$-category $\mathbf{D}_n \otimes [1]$ given in paragraph 1.2.3.4, it is straightforward to see that it induces an equivalence on globes. $\square$

The definitional cocartesian squares

$$\begin{array}{ccc} C \otimes \{1\} & \longrightarrow & C \otimes [1] \\ \downarrow & & \downarrow \\ 1 & \longrightarrow & C \star 1 \end{array} \qquad \begin{array}{ccc} C \otimes \{0\} & \longrightarrow & C \otimes [1] \\ \downarrow & & \downarrow \\ 1 & \longrightarrow & 1 \stackrel{\text{co}}{\star} C \end{array}$$

imply the following proposition:

**Theorem 1.2.3.14.** *There is a natural identification between $1 \stackrel{\text{co}}{\star} [C, 1]$ and the colimit of the following diagram*

$$[1] \vee [C, 1] \longleftarrow [C, 1] \longrightarrow [C \star 1, 1]$$

*There is a natural identification between $[C, 1] \star 1$ and the colimit of the following diagram*

$$[1 \stackrel{\text{co}}{\star} C, 1] \longleftarrow [C, 1] \longrightarrow [C, 1] \vee [1]$$

**Proposition 1.2.3.15.** *Let $C$ be an $(0, \omega)$-category with an atomic and loop free basis. The two following canonical squares are cartesian:*

$$\begin{array}{ccc} 1 & \longrightarrow & 1 \stackrel{\text{co}}{\star} C \\ \downarrow & & \downarrow \\ \{0\} & \longrightarrow & [C, 1] \end{array} \qquad \begin{array}{ccc} 1 & \longrightarrow & C \star 1 \\ \downarrow & & \downarrow \\ \{1\} & \longrightarrow & [C, 1] \end{array}$$

*The five squares appearing in the following canonical diagram are both cartesian and*

57