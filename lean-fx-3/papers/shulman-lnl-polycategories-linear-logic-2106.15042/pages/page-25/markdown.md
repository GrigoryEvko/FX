Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:25

Proof. By structural permutations, the hom-sets of an entries-only LNL polycategory are uniquely determined (up to isomorphism) by those of the form

$$\mathcal{P}(X_1^-, \dots, X_m^-, Y^+)$$

$$\mathcal{P}(X_1^-, \dots, X_m^-, A_1^-, \dots, A_n^-, B_1^+, \dots, B_p^+)$$

for nonlinear objects $X_i, Y$ and linear objects $A_j, B_k$. We can identify these with the hom-sets

$$\mathcal{P}(X_1, \dots, X_m; Y)$$

$$\mathcal{P}(X_1, \dots, X_m \mid A_1, \dots, A_n; B_1, \dots, B_p)$$

in an ordinary LNL polycategory, and the identities, compositions, and structural actions correspond.

Of course, the 2-categorical structure of LNLPoly that we defined in Section 2 can also be transported across this equivalence. A transformation between functors of entries-only LNL polycategories thus has components $\alpha_X \in \mathcal{Q}((HX)^-, (KX)^+)$ and $\alpha_A \in \mathcal{Q}((HA)^-, (KA)^+)$ satisfying suitable axioms.

Henceforth, we will pass freely back and forth between the two definitions, using whichever notation for homsets is more convenient. We can now define a general notion of universal morphism that encompasses all five cases described in Section 2.

**Definition 4.5.** A morphism $f \in \mathcal{P}(\Phi, K)$ in an entries-only LNL polycategory is **universal in** $K$ if for any list of signed objects $\Psi$ such that $(K^\bullet, \Psi)$ is admissible, the composition map $(-\circ_K f): \mathcal{P}(K^\bullet, \Psi) \to \mathcal{P}(\Phi, \Psi)$ is bijective, i.e. for any $h \in \mathcal{P}(\Phi, \Psi)$ there exists a unique $g \in \mathcal{P}(K^\bullet, \Psi)$ such that $g \circ_K f = h$.

In fact, following [Her04, LSR17, BZ20], it is useful to generalize from *universal* morphisms in one multi- or poly-category to *cartesian* ones relative to a functor.

**Definition 4.6.** Given a functor $\pi: \mathcal{P} \to \mathcal{Q}$ of entries-only LNL polycategories, a morphism $f \in \mathcal{P}(\Phi, K)$ is **$\pi$-cartesian in** $K$ if for any list of signed objects $\Psi$ of $\mathcal{P}$ such that $(K^\bullet, \Psi)$ is admissible, the following square is a pullback:

$$\begin{array}{ccc} \mathcal{P}(K^\bullet, \Psi) & \xrightarrow{-\circ_K f} & \mathcal{P}(\Phi, \Psi) \\ \pi \downarrow & & \downarrow \pi \\ \mathcal{Q}(\pi K^\bullet, \pi \Psi) & \xrightarrow{-\circ_{(\pi K)}(\pi f)} & \mathcal{Q}(\pi \Phi, \pi \Psi) \end{array} \tag{4.1}$$

In other words, for any $h \in \mathcal{P}(\Phi, \Psi)$ and $\ell \in \mathcal{Q}(\pi K^\bullet, \pi \Psi)$ such that $\ell \circ_{\pi K} \pi f = \pi h$, there exists a unique $g \in \mathcal{P}(K^\bullet, \Psi)$ such that $g \circ_K f = h$ and $\pi g = \ell$.

Note that if $\mathcal{Q}$ is terminal, both sets on the bottom row of (4.1) are singletons; so the square is a pullback just when the morphism on top is a bijection. Thus, $f$ is universal in $K$ precisely when it is $\pi$-cartesian in $K$ for the unique functor $\pi: \mathcal{P} \to \text{LNLPOLY}$ to the terminal object.

Cartesian morphisms specialize to various notions in the literature:

- For symmetric multicategories, cartesian morphisms with $K$ positive specialize to the "strongly cocartesian" morphisms of [Her04, Remarks 2.2(1)].
- For cartesian multicategories, cartesian morphisms specialize to the cartesian and opcartesian morphisms of [LSR17].