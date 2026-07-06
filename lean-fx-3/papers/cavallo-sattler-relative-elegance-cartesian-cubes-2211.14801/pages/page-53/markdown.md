Relative Elegance and Cartesian Cubes with One Connection

53

As any category of algebras has limits and colimits [ARV10, Proposition 1.21, Theorem 4.5], $\operatorname{Alg}(\mathbf{T})$ has in particular pushouts of spans of surjections.

Corollary 6.4 The Reedy structure on $\operatorname{Alg}(\mathbf{T})_{\mathrm{fin}}^{(\mathrm{inh})}$ is pre-elegant.

Proof The pushout of a span of surjections has cardinality bounded by those of the objects in the span, as surjections are left maps and thus closed under cobase change. ■

Recall that the forgetful functor $U$ preserves limits. While $U$ does not generally preserve colimits, we can show that it preserves pushouts of surjective spans using the technology of sifted colimits.

Definition 6.5 A small category $\mathbf{D}$ is

- filtered if $\operatorname{colim}_{\mathbf{D}}: [\mathbf{D}, \mathbf{Set}] \to \mathbf{Set}$ commutes with finite limits;
- sifted if $\operatorname{colim}_{\mathbf{D}}: [\mathbf{D}, \mathbf{Set}] \to \mathbf{Set}$ commutes with finite products.

A filtered (sifted) colimit is a colimit over a filtered (sifted) category.

Recall that a reflexive coequalizer is a coequalizer of maps $f_0, f_1: A \to B$ with a mutual section, that is, some $d: B \to A$ such that $f_0 d = f_1 d = \operatorname{id}$. Reflexive coequalizers are sifted (but not filtered) colimits [ARV10, Remark 3.2].

Lemma 6.6 Let $F: \mathbf{C} \to \mathbf{D}$ be a functor between regular categories preserving finite limits and sifted colimits. Then $F$ preserves pushouts of regular epi spans.

Proof Let a span $B_0 \stackrel{e_0}{\leftarrow} A \stackrel{e_1}{\twoheadrightarrow} B_1$ in $\mathbf{C}$ be given. We compute the following reflexive coequalizer:

$$A \times_{B_0} A \times_{B_1} A \xrightarrow[\pi_2]{\pi_0} A \xrightarrow{e} B$$

It is straightforward to check, using the characterizations of $e_0, e_1$ as the coequalizers of their kernel pairs, that we have induced maps $B_0 \twoheadrightarrow B \leftrightarrow B_1$ exhibiting $B$ as the pushout of our span. As $F$ preserves the diagram above, it preserves this pushout. ■

Corollary 6.7 $U: \operatorname{Alg}(\mathbf{T}) \to \mathbf{Set}$ preserves pushouts of surjective spans.

Proof $U$ preserves limits and sifted colimits [ARV10, Proposition 2.5]. ■

We now assume that any $\mathbf{T}$-algebra free on a finite set has a finite underlying set. In this case, the elegant core coincides with the class of perfectly presentable (also called strongly finitely presentable) algebras.

Definition 6.8 (ARV10, Definition 5.3) An object $A$ of a category $\mathbf{C}$ is

- finitely presentable if $\mathbf{C}(A, -): \mathbf{C} \to \mathbf{Set}$ preserves filtered colimits;

2025/10/16 00:43