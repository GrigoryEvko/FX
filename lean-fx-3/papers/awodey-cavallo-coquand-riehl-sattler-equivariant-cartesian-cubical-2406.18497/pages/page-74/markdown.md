**Corollary 6.2.16.** *Let A be an Eilenberg–Zilber category and consider a parallel pair of functors $U, V: \mathsf{Set}^{\mathsf{A}^{\mathsf{op}}} \to \mathsf{M}$ valued in a model category M together with a natural transformation $\alpha: U \Rightarrow V$. Suppose that U and V preserve colimits and send monomorphisms in K to cofibrations in M. Then if the components of $\alpha$ at quotients of representables by subgroups of their automorphism groups are weak equivalences, then all components of $\alpha$ are weak equivalences.*

*Proof.* Note that the components of $\alpha$ at a presheaf $X$ are obtained by Leibniz application of $\alpha$ at the monomorphism $\emptyset \to X$. The result now follows by combining Lemma 6.2.13, which says that the monomorphisms in $\mathsf{Set}^{\mathsf{A}^{\mathsf{op}}}$ are generated under coproduct, pushout, transfinite composition, and right cancelation among monomorphisms by the maps $\emptyset \to \mathsf{A}_{/H}^{\mathsf{a}}$, with Lemma 6.2.15, which says that the class of monomorphisms whose Leibniz applications are weak equivalences has these closure properties. $\square$

**Corollary 6.2.17.** *Let A be an Eilenberg–Zilber category for which $\mathsf{Set}^{\mathsf{A}^{\mathsf{op}}}$ admits a model structure whose cofibrations are the monomorphisms in which the quotients $\mathsf{A}_{/H}^{\mathsf{a}}$ of representables by subgroups of their automorphism groups are weakly contractible. Then if $U, V: \mathsf{Set}^{\mathsf{A}^{\mathsf{op}}} \to \mathsf{M}$ define a pair of left Quillen functors that preserve the terminal object, then any natural transformation $\alpha: U \Rightarrow V$ is a natural weak equivalence.*

*Proof.* By Ken Brown's lemma, left Quillen functors from $\mathsf{Set}^{\mathsf{A}^{\mathsf{op}}}$ that preserve the terminal object preserve weakly contractible cofibrant objects. Now from the naturality square associated to a weakly contractible cofibrant object $X$

$$\begin{array}{ccc} UX & \xrightarrow{\alpha_X} & VX \\ \updownarrow_{\downarrow} & & \updownarrow_{\downarrow} \\ U* & = & V* \end{array}$$

and the 2-of-3 property, we see that the component $\alpha_X$ is a weak equivalence. By Corollary 6.2.16, if the components of $\alpha$ at quotients of representables are weak equivalences, then $\alpha$ is a natural weak equivalence. So the result follows. $\square$

Note that $i^*$ preserves the terminal object, as a right adjoint, as does $i_!$, since in both domain and codomain it is representable and $i[0] := [0, 1]^0$.

**Proposition 6.2.18.** *The functors*

$$\begin{array}{ccc} & \xleftarrow{i_!} & \\ \mathsf{cSet} & \xleftarrow{\quad} & \mathsf{sSet} \\ & \searrow & \searrow \\ & i^* & \end{array}$$

*are left Quillen equivalences.*

*Proof.* The unit and counit of these adjunctions each define natural transformations between left Quillen adjoints that preserve the terminal object. As the domain and codomain of these functors are categories of presheaves for Eilenberg–Zilber categories equipped with model structures for which all objects are cofibrant and quotients of representables are contractible, Corollary 6.2.17 applies to prove that both the unit and counit are natural weak equivalences. $\square$

**6.3. The equivariant model structure is the test model structure.** Finally, we show that the equivariant model structure coincides with the test model structure.

The cartesian cube category is a *strict test category* [BM17], so cartesian cubical sets admits a model structure, conjectured to exist by Grothendieck [Gro84] and established at this level of generality by Cisinski [Cis06], that presents classical homotopy theory. In Cisinski's model structure on presheaves over a test category—referred to as a **test model structure** below—the cofibrations

74