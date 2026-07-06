STRICT UNIVERSES FOR GROTHENDIECK TOPOI

9

2.2.1. DEFINITION. We define $\hat{S}_{\vee}$ to consist of morphisms $f: X \longrightarrow Y$ such that for each cartesian square of the following shape, the presheaf $y^*X$ is (essentially) $\vee$-valued:

$$\begin{array}{c} y^*X \longrightarrow X \\ \downarrow \quad \downarrow f \\ y(C) \longrightarrow Y \end{array}$$

Explicitly, for each $D: \mathcal{C}$ the set $(y^*X)_D$ must be $\vee$-small.

2.2.2. REMARK. We may equivalently describe $\hat{S}_{\vee}$ as the class of maps $f: X \longrightarrow Y$ such that the fibers of $f$ over representables are $\vee$-small.

Again, it remains to show that this class satisfies the expected axioms. (U1–4,6,7) follow through calculation (taking advantage of the standard construction of $f_*g$ for (U4) and $\Omega$ for (U6)). Hofmann and Streicher [HS97] show that $\hat{S}_{\vee}$ satisfies (U5) with a generic map $\varpi: \tilde{U} \longrightarrow U$. The construction of $\varpi$ is highly dependent on $\Pr(\mathcal{C})$ being a presheaf category, taking advantage of the correspondence $\Pr(\mathcal{C})_{/y(C)} \simeq \Pr(\mathcal{C}_{/C})$ which represents the codomain fibration as a strict 2-functor rather than the usual pseudofunctor. This correspondence restricts to presheaves valued in the full subcategory of Set spanned by elements of $\vee$ to induce an equivalence $\Pr_{\vee}(\mathcal{C})_{/y(C)} \simeq \Pr_{\vee}(\mathcal{C}_{/C})$. We use this to define $U_C$ as follows:

$$U_C = \Pr_{\vee}(\mathcal{C}_{/C})$$

The generic family $\varpi$ is most directly defined as a presheaf over $\mathsf{Elt}(U)$, again taking advantage of the equivalence $\Pr(\mathcal{C})_{/U} \simeq \Pr(\mathsf{Elt}(U))$

$$\varpi_{(C,X)} = X_{(C,\mathsf{id})}$$

The following is a result of Hofmann and Streicher [HS97].

2.2.3. THEOREM. $\varpi$ satisfies (U5).

PROOF. Fix a map $f: Q \longrightarrow X \in \hat{S}_{\vee}$. We must show that there exists some cartesian square $f \longrightarrow \varpi$. First, let us note that $f: Q \longrightarrow X$ induces a presheaf $F: \Pr(\mathsf{Elt}(X))$ and our assumption that $f \in \hat{S}_{\vee}$ ensures that $F$ is essentially $\vee$-small. In particular, we may choose $F' \cong F$ such that $F'$ belongs to the subcategory $\Pr_{\vee}(\mathsf{Elt}(X))$.

We will now construct a cartesian square $f \longrightarrow \varpi$ by defining a morphism explicitly $q: X \longrightarrow U$ and then argue that $q^*\varpi = f$. To this end, let us fix $C: \mathcal{C}$ along with $x \in X_C$ and define $q_C(x) \in U_C = \Pr_{\vee}(\mathcal{C}_{/C})$:

$$q_C(x)_{(D,c)} = F'(D, x \cdot c)$$

The computation that $q$ organizes into a natural transformation is routine.

It remains only to argue that $q^*\varpi$ is isomorphic to $f$. Examining the definition of $\varpi$, it is easiest to argue this by once more passing to $\Pr(\mathsf{Elt}(X))$ and showing that $q^*\varpi \cong F$. However, by definition $q^*\varpi$ is isomorphic to $F'$ which is in turn isomorphic to $F$. ■