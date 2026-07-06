44

E. Cavallo and C. Sattler

freely on $\mathbf{R}^{-}(r, -)$, it is the left Kan extension along some functor $A \to \mathbf{R}[n]$ of some $F: A \to \mathbf{Set}$ with $A$ a set. Recall that epimorphisms are characterized levelwise in Set-valued functors. By adjoint transposition, it thus suffices to show that $F$ is epi-projective. Since $A$ is a set, this just means that $F$ is levelwise epi-projective. And in Set, every object is epi-projective.

Corollary 5.20 Suppose that isos act freely on lowering maps in $\mathbf{R}$. Given a Reedy monic $f \in \mathrm{PSh}(\mathbf{R})^{\rightarrow}$, the map $\mathfrak{o}^n\mathbf{R} \widehat{\otimes}_{\mathbf{R}[n]^{\oplus}} \widehat{\ell}_n f$ is monic for all $n \in \mathbb{N}$.

Proof We have $(\mathfrak{o}^n\mathbf{R} \widehat{\otimes}_{\mathbf{R}[n]^{\oplus}} \widehat{\ell}_n f)_r = \mathfrak{o}^n\mathbf{R}_r \widehat{\otimes}_{\mathbf{R}[n]^{\oplus}} \widehat{\ell}_n f$ for every $r \in \mathbf{R}$. We know $\mathfrak{o}^n\mathbf{R}_r$ is epi-projective by Lemma 5.19, and $\widehat{\ell}_n f$ is monic by assumption, so their Leibniz weighted colimit is monic by Proposition 5.18.

### 5.1.3 Eilenberg-Zilber decompositions

The Reedy monomorphisms with initial domain can be characterized more simply: an object $X$ is Reedy monic exactly if every element of $X$ writes uniquely up to isomorphism as a degeneracy of a non-degenerate element of $X$. We are not aware of a proof of this precise statement (Lemma 5.24) in the literature, though we would be surprised if it were unknown. We use Cisinski's term "Eilenberg-Zilber decomposition" [Cis06, Proposition 8.1.13] for what Berger and Moerdijk call standard decompositions.

Definition 5.21 Let $X \in \mathrm{PSh}(\mathbf{R})$. We say that $x \in X_r$ is non-degenerate when every lowering map $e: r \xrightarrow{\sim} s$ admitting an $x' \in X_s$ with $x'e = x$ is an isomorphism. An Eilenberg-Zilber (EZ) decomposition of $x \in X_r$ is a pair $(e, x')$ where $x' \in X_s$ is non-degenerate, $e: r \to s$ is a lowering map, and $x = x'e$. We regard two EZ decompositions $(e_0, x_0')$ and $(e_1, x_1')$ of $x$ as isomorphic when there exists an isomorphism $\theta: s_0 \cong s_1$ in $\mathbf{R}$ such that $x_0'\theta = x_1'$ and $e_0 = e_1\theta$. We say $X$ has unique EZ decompositions when any two EZ decompositions of any element of $X$ are isomorphic.

Remark 5.22 Every element of a presheaf admits at least one EZ decomposition: for any $x \in X_r$ there exists a minimal $n \in \mathbb{N}$ such that $x$ factors though a lowering map to an object of degree $n$, and any such factorization is an EZ decomposition.

Proposition 5.23 (RV14, Observation 3.23) Given $X \in \mathrm{PSh}(\mathbf{R})$ and $r \in \mathbf{R}$, we have an isomorphism

$$\begin{array}{c} L_r X_- \quad \widehat{\ell}_r X_- \\ \downarrow \\ \downarrow^W \\ L_r X \quad \xrightarrow{\widehat{\ell}_r X} X_r, \end{array}$$

where $X_- \in \mathrm{PSh}(\mathbf{R}^-)$ is the restriction of $X$ along the Reedy category inclusion $\mathbf{R}^- \to \mathbf{R}$.

Lemma 5.24 A presheaf $X \in \mathrm{PSh}(\mathbf{R})$ is Reedy monic if and only if it has unique EZ decompositions.

2025/10/16 00:43