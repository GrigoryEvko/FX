Our convergence condition on our $S$ and $\mathcal{M}$ is loosely analogous to asking that $S$ preserves isomorphism-tightness of $(\mathcal{M}, \kappa)$-cones. However, we do not assume that $\mathcal{M}$ is the right class of an orthogonal factorization system, while conversely Kelly does not assume that $\mathcal{M}$ is closed under transfinite compositions. We also use the property in a different way. Our conditions ensure that the diagram (2.1) factors through our $\mathcal{M}$, allowing us to apply the convergence criterion to that diagram directly. By contrast, Kelly's argument (see, e.g., the proof of [Kel80, Proposition 4.1]) does not require that (2.1) factors through his $\mathcal{M}'$; rather, he derives auxiliary diagrams which do factor through $\mathcal{M}'$ and uses the tightness-preservation property with these diagrams to arrive indirectly at the convergence of (2.1).

## 2.3 Pointed endofunctors

For the construction of free algebras and monads on arbitrary pointed endofunctors, we need not only sequential colimits but also pushouts. We now introduce the notion of backdrop that we will use throughout this article:

Definition 2.3.1. Let $\mathcal{M}$ be a wide subcategory of a category $\mathcal{E}$. We say that $\mathcal{M}$ is closed under cobase change in $\mathcal{E}$ when for every span consisting of morphisms $A \to B$ in $\mathcal{M}$ and $A \to X$ in $\mathcal{E}$, there is a pushout square of the form

$$\begin{array}{c} A \longrightarrow X \\ \mathcal{M} \ni \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B \longmapsto Y \end{array}$$

in $\mathcal{E}$.

Definition 2.3.2. Let $\mathcal{E}$ be a category and $\kappa > 0$ be a limit ordinal. A wide subcategory $\mathcal{M}$ of $\mathcal{E}$ is a $\kappa$-backdrop when

- (a) $\mathcal{M}$ has colimits of $(1 + \alpha)$-chains in $\mathcal{E}$ for $\alpha < \kappa$;
- (b) $\kappa$-chains in $\mathcal{M}$ have colimits in $\mathcal{E}$;
- (c) $\mathcal{M}$ is closed under cobase change in $\mathcal{E}$.

Given $F: \mathcal{E}_1 \to \mathcal{E}_2$ and $\kappa$-backdrops $\mathcal{M}_1$ and $\mathcal{M}_2$ in $\mathcal{E}_1$ and $\mathcal{E}_2$ respectively, we say that $F$ is a $\kappa$-backdrop-preserving functor $(\mathcal{E}_1, \mathcal{M}_1) \to (\mathcal{E}_2, \mathcal{M}_2)$ when $F$ sends $\mathcal{M}_1$ into $\mathcal{M}_2$, and preserves colimits of $(1 + \alpha)$-chains in $\mathcal{M}_1$ for $\alpha < \kappa$, colimits of $\kappa$-chains in $\mathcal{M}_1$, and cobase changes of maps in $\mathcal{M}_1$.

Example 2.3.3. For any adhesive [LS05] and $\kappa$-exhaustive [Shu15, §3] category $\mathcal{E}$ (e.g., any topos), the class of monomorphisms in $\mathcal{E}$ is a $\kappa$-backdrop.

Example 2.3.4. If $\mathcal{E}$ is a category with coproducts, then the class of complemented monomorphisms in $\mathcal{E}$ is an $\omega$-backdrop. As noted in Remark 2.2.7, $\mathcal{E}$ has colimits of $\omega$-chains of complemented monomorphisms. Cobase changes of along complemented monomorphisms can likewise be computed using coproducts and complements:

$$\begin{array}{c} A \xmapsto{m} C \\ f \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B \longmapsto B \sqcup (C \setminus A). \end{array}$$

Given another category $\mathcal{C}$, the functor category $[\mathcal{C}, \mathcal{E}]$ has the class of levelwise complemented monomorphisms as an $\omega$-backdrop, since the relevant colimits are computed levelwise. In a constructive metatheory without quotients (see Appendix A), we are interested in particular in the case where $\mathcal{E} = \mathbf{Set}$.

16