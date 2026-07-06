**Lemma 4.2.7.** *The cubical species $\mathbb{I}$ is tiny.*

*Proof.* Recall that $\mathbb{I}(c) = \square(-, c) \in \mathsf{cSet}$ is representable. Since $\square$ has binary products, representables in $\mathsf{cSet}$ are tiny. Now $\mathbb{I}$ is tiny by Corollary 4.1.5. $\square$

**4.3. The cylindrical premodel structure on cubical species.** We determine a pair of (algebraic) weak factorization systems that constitute a premodel structure on the cubical species and prove that it is cylindrical, with adjoint functorial cylinder represented by the interval object

$$\mathbb{1} \xrightarrow[\delta_1]{\delta_0} \mathbb{I} \xrightarrow{!} \mathbb{1}$$

where the points $\delta_0, \delta_1$ correspond to the constant sequences $\vec{0}, \vec{1}$ of Remark 4.2.6.

As a presheaf topos, the category $\mathsf{cSet}^{\mathbb{I}}$ has a subobject classifier $\top: \mathbb{1} \mapsto \Omega$, which we can describe explicitly as follows.

**Lemma 4.3.1.** *For $n, k \in \mathbb{N}$, $k \ge 1$, elements $\chi_c: \mathbb{F}_k I^n \to \Omega$ of the subobject classifier correspond bijectively to subobjects $c: C \mapsto I^n$ of the $n$-cube.*

*Proof.* By definition, an element $\chi_c: \mathbb{F}_k I^n \to \Omega$ corresponds to a subobject of the representable cubical species $\mathbb{F}_k I^n$. Since $\mathbb{F}_k I^n$ is concentrated in degree $k$ and has a free $\Sigma_k$-action, its subobject must have these properties as well. Thus, we see that the subobject has the form $\mathbb{F}_k c: \mathbb{F}_k C \mapsto \mathbb{F}_k I^n$ for a necessarily unique subobject $c: C \mapsto I^n$ of the $n$-cube. $\square$

**Definition 4.3.2.** As the **cofibrations** we take the monomorphisms, which are classified (up to equivalence) by the subobject classifier $\top: \mathbb{1} \mapsto \Omega$. The **trivial fibrations** are then the maps with the right lifting property against all monomorphisms.

As we saw in §2.2, the cofibrations and trivial fibrations form a weak factorization system. By Lemma 2.2.10, we can recognize the trivial fibrations as the class underlying a locally representable and relatively acyclic notion of fibred structure $\mathbb{TF}$.

We now turn to the (trivial cofibration, fibration) weak factorization system. The fibrations will be the unbiased fibrations of Definition 3.6.7(ii)—see Theorem 4.3.14—which we now describe explicitly. The fibrations will be determined by the trivial fibrations, by Leibniz pullback application of the evaluation natural transformation $\mathrm{ev}: (-)^{\mathbb{I}} \times \mathbb{I} \Rightarrow (-)$ involving the interval $\mathbb{I}$. Equivalently, we may describe them as given by right lifting against a category of generating trivial cofibrations constructed using the universal subobject $\top: \mathbb{1} \to \Omega$ and the “generic point” $\delta: \mathbb{I} \to \mathbb{I} \times \mathbb{I}$—see Definition 4.3.11. With the latter description, we can obtain a functorial factorization (indeed, an awfs) constructively using Garner’s algebraic small object argument.

**Definition 4.3.3.** As a map in the slice category $\mathsf{cSet}_{/\mathbb{I}}^{\mathbb{I}}$, the diagonal $\delta: \mathbb{I} \to \mathbb{I} \times \mathbb{I}$ defines an additional point of $\mathbb{I}$, called the **generic point**.

The morphisms $\top: \mathbb{1} \to \Omega$ in $\mathsf{cSet}_{/\Omega}^{\mathbb{I}}$ and $\delta: \mathbb{I} \to \mathbb{I} \times \mathbb{I}$ in $\mathsf{cSet}_{/\mathbb{I}}^{\mathbb{I}}$ can be reindexed to lie in the common slice $\mathsf{cSet}_{/\Omega \times \mathbb{I}}^{\mathbb{I}}$. Their pushout product there defines a family of maps $\top \hat{\times}_{\Omega \times \mathbb{I}} \delta$ internally

44