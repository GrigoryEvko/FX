DOUBLY WEAK DOUBLE CATEGORIES

33

that commute with the representability isomorphisms:

$$\begin{array}{c} F1_A \\ \phi_A^H \\ 1_{FA} \\ \cong \\ FA \end{array} = \begin{array}{c} F1_A \\ F(\cong) \\ FA \end{array} \quad F1_A \quad \phi_A^H 1_{FA} \cong FA = F1_A \quad F(\cong) \quad FA$$

However, since the representability cells are also isomorphisms, the conditions required above uniquely determine each invertible cell $\phi$ (as the composite of two representability cells). The case of bicategories is similar. Thus the pseudo-morphisms are simply functors of the underlying implicit structures, recovering the categories **W-2-Cat** and **WDblCat** from Section 2 and Section 3:

**Proposition 6.8.** *If $X$ and $Y$ are bicategories, then every functor $F: X \to Y$ of implicit 2-categories has a unique structure of pseudo $T_2^w$-morphism.*

*Similarly, if $X$ and $Y$ are doubly weak double categories, then every functor $F: X \to Y$ of implicit double categories has a unique structure of pseudo $T_d^w$-morphism.*

**Corollary 6.9.** *The 2-monads $T_2^w$ on $\mathcal{I}$-2-Cat, and $T_d^w$ on $\mathcal{IDblCat}$, are pseudo-idempotent. Therefore, an icon between bicategories or doubly weak double categories is nothing more than an icon between their underlying implicit 2-categories or implicit double categories.*

*Proof.* The first statement is by definition of “pseudo-idempotent”. The second follows from [KL97, Proposition 6.7].

*Remark 6.10.* In particular, every lax or colax $T_2^w$- or $T_d^w$-morphism is automatically pseudo. We could obtain nontrivial notions of lax and colax functors by using the alternative base 2-category suggested in Remark 6.5.

*Remark 6.11.* The same arguments apply for the 2-monads whose algebras are strict 2-categories, strict double categories, and pseudo double categories. In the fully strict case it is also sensible to consider *pseudo algebras*; these yield “unbiased” bicategories and a similar notion of “unbiased doubly weak double category”. General 2-monadic coherence techniques as in [Pow89, Lac02a, Shu12] can be adapted to show that every such unbiased structure is equivalent to a strict one.

We end this section by characterizing the relevant equivalences more explicitly, and proving a coherence theorem for (biased) doubly weak double categories.

**Lemma 6.12.** *A functor of implicit double categories $F: \mathbf{C} \to \mathbf{D}$ is an equivalence in the 2-category $\mathcal{IDblCat}$ if and only if it is*

- *byjective on 0-cells,*
- *locally essentially surjective on horizontal and vertical 1-cells, and*
- *byjective on 2-cells per boundary of 1-cells in $\mathbf{C}$.*

*Therefore, a functor of doubly weak double categories is an equivalence in the 2-category $\mathcal{WDblCat}$ if and only if it satisfies these same conditions.*