Relative Elegance and Cartesian Cubes with One Connection

51

Definition 5.43 A map $m: X \to Y$ in PSh(R) reflects degeneracy if has the right lifting property against lowering maps $e: \not\perp r \xrightarrow{\sim} \not\perp s$.

This means that for any $x \in X_r$, if $m_r(x)$ factors through some $e: \not\perp r \xrightarrow{\sim} \not\perp s$, then $x$ also factors through $e$.

Lemma 5.44 Let $\mathbf{R}$ be a Reedy category, let $Y \in \mathrm{PSh}(\mathbf{R})$ be Reedy monic, and let $m: X \mapsto Y$ be a degeneracy-reflecting monomorphism. Then $m$ is Reedy monic.

Proof By Proposition 5.23, it suffices to show, for any $r \in \mathbf{R}$, that the pushout gap map in the naturality square

$$\begin{array}{c} L_r X_- \to X_r \\ \downarrow \qquad \qquad \downarrow \\ L_r Y_- \to Y_r \end{array}$$

is monic. The bottom and right maps are monic by assumption. Because $m$ reflects degeneracy, the square is a weak pullback, i.e., the pullback gap map is surjective. This means that the pushout gap map, seen as an object over $Y_r$, is the union of the subobjects given by the bottom and right maps.

Corollary 5.45 If $i: \mathbf{C} \to \mathbf{R}$ is relatively elegant, then $i_*m$ is Reedy monic for every $m: X \mapsto Y$ in PSh(C).

Proof By Lemma 5.44, it suffices to show that $i_*m$ reflects degeneracy. For any $e: r \xrightarrow{\sim} s$, $N_{\ell}e$ is epic by Lemma 5.37, so has left lifting against monos. By transposition, $e$ has left lifting against $i_*m$.

In any presheaf category, all monomorphisms can be presented as cell complexes (transfinite composites of cobase changes of coproducts) of monomorphisms whose codomains are quotients of representables [Cis06, Proposition 1.2.27]. With Corollary 5.45, we can give an alternative—not necessarily comparable—set of generators in terms of the boundary inclusions in $\mathbf{R}$.

Theorem 5.46 If $i: \mathbf{C} \to \mathbf{R}$ is relatively elegant, then every monomorphism in PSh(C) is a cell complex of maps of the form $i^*(\mathfrak{o}^n\mathbf{R} \circledast_{\mathbf{R}[n]^{\oplus}}(\not\perp r/H))$ where $r \in \mathbf{R}$ and $H \leq \mathrm{Aut}_{\mathbf{R}}(r)$.

Proof Let $m: X \mapsto Y$ in PSh(C). By Corollary 5.16, $i_*m$ has a cellular presentation by maps of the form $\mathfrak{o}^n\mathbf{R} \circledast_{\mathbf{R}[n]^{\oplus}} \widehat{\ell}_n(i_*m)$; by Corollary 5.45, each $\widehat{\ell}_n(i_*m)$ is monic in PSh(R[n]). In PSh(R[n]), any monomorphism is a cell complex of maps of the form $0 \mapsto \not\perp r/H$ for some $r \in \mathbf{R}[n]$ and $H \leq \mathrm{Aut}_{\mathbf{R}}(r)$, because PSh(R[n]) is Boolean and any R[n]-set decomposes as a coproduct of orbits. By [RV14, Lemma 5.7], it follows that $i_*m$ is a cell complex of maps $\mathfrak{o}^n\mathbf{R} \circledast_{\mathbf{R}[n]^{\oplus}}(0 \mapsto \not\perp r/H)$. Finally, $i^*$ preserves colimits and thus cell complexes.

2025/10/16 00:43