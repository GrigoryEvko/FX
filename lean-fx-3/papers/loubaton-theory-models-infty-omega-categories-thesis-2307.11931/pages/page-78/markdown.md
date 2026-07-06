CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

Proof. Let $I_n$ be the category indexing the previous diagram. We denote $i_0, j_0, \ldots, i_{n-1}, j_{n-1}, i_n$ it's objects. The projective model structure on $\operatorname{Fun}(I_n, C)$ is given by functor $G$ such that for any $k < n$, $F(j_k) \to F(i_k)$, $F(j_k) \to F(i_{k+1})$ are monomorphisms, and such that for any $0 < k < n$, $F(j_k) \coprod F(j_{k+1}) \to F(i_k)$ is a monomorphism. Remark that such presheaves verify the condition given in the statement of the proposition.

We will show on induction on $n$ that a natural transformation $\psi$ between two diagrams $F, G : I_n \to C$ that fulfills the desired condition induces a weak equivalence between their colimits. As we can always chose $F$ to be the cofibrant replacement of $G$ in the projective model structure on $\operatorname{Fun}(I_n, C)$, it will imply the desired result.

The case $n = 1$ is proposition 2.1.1.3. Suppose now the result is true at the stage $(n - 1)$ and let $\psi$ be a weakly invertible natural transformation between two diagram $F, G : I_n \to C$ that fulfills the desired condition. We denote by $\iota : I_{n-1} \to I_n$ the canonical inclusion that sends $i_k(\text{resp. } j_k)$ on $i_k(\text{resp. } j_k)$ for $k < n$ (resp. $k < n - 1$). We then have a diagram

$$\begin{array}{c} \operatorname{colim}_{I_{n-1}} F \circ \iota \longleftarrow F(j_{n-1}) \hookrightarrow F(i_n) \\ \sim \downarrow \qquad \qquad \qquad \sim \downarrow \qquad \qquad \sim \downarrow \\ \operatorname{colim}_{I_{n-1}} G \circ \iota \longleftarrow G(j_{n-1}) \hookrightarrow G(i_n) \end{array}$$

where all arrows labeled by $\sim$ are weak equivalences. Remark furthermore that the limit of the two lines are respectively $\operatorname{colim}_{I_n} F$ and $\operatorname{colim}_{I_n} G$. A last application of proposition 2.1.1.3 concludes the proof.

2.1.1.6. The definition of elegant Reedy category is given in paragraph 1.1.2.5. As all the presheaves categories that we will encounter through this text are presheaves on elegant Reedy categories, we will use freely the following theorem:

Theorem 2.1.1.7 (Hirschhorn). We suppose that $C$ is a simplicial model category. Let $A$ be a elegant Reedy category, and $F : A \to C$ a functor such that the induced morphism $\operatorname{colim}_{\partial a} F \to F(a)$ is a monomorphism for any object $a$. The object $\operatorname{colim}_A F$ is the homotopy colimit of $F$. In particular, if $C$ is $\operatorname{Psh}(A)$, every object $X$ is the homotopy colimit of the diagram $A_{/X} \to A \to \operatorname{Psh}(A)$.

Proof. Using the characterization of elegant Reedy category given by proposition 3.8 of [BR13b], and [Hir03, proposition 15.10.2], it's easy to see that they have fibrant constant in the sens of [Hir03, definition 15.10.1]. We can then apply the theorem 19.9.1 of [Hir03].

2.1.1.8. A model structure is nice if it is simplicial, combinatorial, cartesian and its cofibrations are monomorphisms.

68