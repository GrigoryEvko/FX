CHAPTER 2. STUDY OF COMPLICIAL SETS

condition. We denote by $\iota : I_{n-1} \to I_n$ the canonical inclusion that sends $i_k(\text{resp. } j_k)$ on $i_k(\text{resp. } j_k)$ for $k < n$ (resp. $k < n-1$). We then have a diagram

$$\begin{array}{c} \operatorname{colim}_{I_{n-1}} F \circ \iota \longleftarrow F(j_{n-1}) \longmapsto F(i_n) \\ \sim \Big\downarrow \qquad \qquad \qquad \sim \Big\downarrow \qquad \qquad \sim \Big\downarrow \\ \operatorname{colim}_{I_{n-1}} G \circ \iota \longleftarrow G(j_{n-1}) \longmapsto G(i_n) \end{array}$$

where all arrows labeled by $\sim$ are weak equivalences. Remark furthermore that the limit of the two lines are respectively $\operatorname{colim}_{I_n} F$ and $\operatorname{colim}_{I_n} G$. A last application of proposition 2.1.1.2 concludes the proof. $\square$

**Definition 2.1.1.6.** A model structure is *nice* if it is simplicial, combinatorial, cartesian and its cofibrations are monomorphisms.

The definition of elegant Reedy category and of Reedy cofibrant diagram are given in definitions 1.1.2.8 and 1.1.3.1. As all the presheaves categories that we will encounter through this text are presheaves on elegant Reedy categories, we will use freely the following theorem:

**Theorem 2.1.1.7** (Hirschhorn). *We suppose that $C$ is a nice model category. Let $A$ be a elegant Reedy category, and $F : A \to C$ a Reedy cofibrant diagram. The object $\operatorname{colim}_A F$ is the homotopy colimit of $F$. In particular, if $C$ is $\operatorname{Psh}(A)$, every object $X$ is the homotopy colimit of the diagram $A_{/X} \to A \to \operatorname{Psh}(A)$.*

*Proof.* Using the characterization of elegant Reedy category given by proposition 3.8 of [BR13], and [Hir03, proposition 15.10.2], it's easy to see that they have fibrant constant in the sens of [Hir03, definition 15.10.1]. We can then apply the theorem 19.9.1 of [Hir03]. $\square$

**Proposition 2.1.1.8.** *Weak equivalences of a nice model category form a precomplete class in the sense of definition 1.1.3.2.*

*Proof.* The first two conditions of definition 1.1.3.2 are obviously fulfilled by the class of weak equivalences. The last one follows from theorem 2.1.1.7. $\square$

**Notation 2.1.1.9.** Let $\_ \square \_ : C \times D \to E$ be a bifunctor. If $f : a \to b$ and $g : x \to y$ are respectively morphisms of $C$ and $D$, we will note by $f \stackrel{\circ}{=} g$ the induced morphism $a \square y \coprod_{a \square x} b \square x \to b \square y$.

**Proposition 2.1.1.10.** *Let $A$ be a nice model structure and $S$ a set of cofibrations. There exists a model structure $A_S$ on the same category, and a left Quillen adjoint $L : A \to A_S$, such that an object is fibrant in $A_S$ if and only if it is fibrant in $A$ and has the right lifting property against all morphisms of shape $i \stackrel{\circ}{\times} f$ where $i$ is a cofibration and $f$ in $S$. Moreover, a left Quillen functor $F : A \to C$ lifts to $A_S$ if and only if for any cofibration $i$ and morphism $f \in S$, $F(i \stackrel{\circ}{\times} f)$ is a weak equivalence.*

*Proof.* This is [[Lur09, proposition A.3.7.3]].

**Corollary 2.1.1.11.** *Let $A$, $C$ be two nice model categories, $F : A \to C$ a left Quillen functor, $S$ a set of cofibrations and $T$ a set of morphisms such that for any cofibrations $i$ and morphisms $f \in S$, the morphism $i \stackrel{\circ}{\times} f$ is included in the smallest saturated class stable by two out of three, containing weak equivalences and $T$. Then a left Quillen functor $F : A \to C$ lifts to $A$ if and only if it sends morphisms of $T$ to weak equivalences.*

64