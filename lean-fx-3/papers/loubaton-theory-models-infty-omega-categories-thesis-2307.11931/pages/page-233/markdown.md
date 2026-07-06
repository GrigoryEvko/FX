4.3. GRAY OPERATIONS

For the right hand square, all the objects are strict according to proposition 4.3.3.12. We can then show the cartesianess in $(0, \omega)$-cat, where it follows from lemma 1.2.3.16. $\square$

**Lemma 4.3.3.16.** *Let $C$ be an $(\infty, \omega)$-category, $a$ a globular sum, and $a \to C$ any morphism. The following canonical square is cartesian:*

$$\begin{array}{ccc} C \coprod_a a \otimes [1] & \longrightarrow & C \coprod_a a \star 1 \\ \downarrow & & \downarrow \\ 1 \stackrel{co}{\star} a & \longrightarrow & [a, 1] \end{array}$$

*Proof.* For any $(\infty, \omega)$-category $D$, the first square of proposition 4.3.3.15 implies that the following square is cartesian

$$\begin{array}{ccc} D \otimes \{0\} & \longrightarrow & D \otimes \{0\} \\ \downarrow & & \downarrow \\ 1 \stackrel{co}{\star} a & \longrightarrow & [a, 1] \end{array}$$

The statement then follows from proposition *op cit* and the preservation of colimit of the pullback along the morphism $1 \stackrel{co}{\star} a \to [a, 1]$ stated by corollary 5.2.3.12. $\square$

**Proposition 4.3.3.17.** *Let $C$ be a strict $(\infty, \omega)$-category, $a$ a globular sum, and $a \to C$ any morphism. The $(\infty, \omega)$-category $C \coprod_a a \otimes [1]$ is strict. In particular $a \otimes [1]$ is strict.*

*Proof.* According to propositions 4.3.3.2 and 4.3.3.12, the two lower objects and the upper right one of the cartesian square of lemma 4.3.3.16 are strict whenever $C$ is. As strict object are stable under pullback, this concludes the proof. $\square$

**4.3.3.18.** We combine the proposition 4.3.3.12 and 4.3.3.17 in the following theorem:

**Theorem 4.3.3.19.** *Let $C$ be an $(\infty, \omega)$-category, $a$ a globular sum, and $f : a \to C$ any morphism. The $(\infty, \omega)$-categories*

$$1 \stackrel{co}{\star} a \coprod_a C \quad C \coprod_a a \otimes [1] \quad C \coprod_a a \star 1$$

*are strict whenever $C$ is. In particular, $a \otimes [1]$, $a \star 1$ and $1 \stackrel{co}{\star} a$ are strict.*

**Corollary 4.3.3.20.** *Let $a$ be a globular sum, and $K$ an order set, viewed as an $(\infty, 1)$-category. The $(\infty, \omega)$-category $a \otimes K$ is strict.*

223