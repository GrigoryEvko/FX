STRICT UNIVERSES FOR GROTHENDIECK TOPOI

25

3.3.12. LEMMA. For any strongly inaccessible $\lambda \triangleright \mathfrak{c}(\mathcal{E})$, there exists a $\lambda$-small set of monomorphisms $\mathcal{I}$ generating all monomorphisms in $\mathcal{E}$ under pushout, transfinite composition, and retracts. Moreover, the domains and codomains of morphisms in $\mathcal{I}$ are $\lambda$-compact.

PROOF. Beke [Bek00, Proposition 1.12] shows that the collection of sub-quotients of representables $J$ generate all monomorphisms in $\operatorname{Pr}(\mathcal{C})$. Explicitly, $J$ is the collection of monomorphisms $A \mapsto B$ where $B$ is the quotient of a representable $\mathbf{y}(C)$. As $\operatorname{Pr}(\mathcal{C})$ is both well-powered and co-well-powered there is essentially a set of such monomorphisms.

A quotient of a representable $\mathbf{y}(C)$ is determined by a morphism $\mathbf{y}(C) \times \mathbf{y}(C) \longrightarrow \Omega$. As $\lambda > |\mathcal{C}|$, $\Omega$ is $\lambda$-small and there is a $\lambda$-small set of representables therefore $J$ may be chosen to be $\lambda$-small. Finally, the domains and codomains of monomorphisms in $J$ are $\lambda$-small, since they are subquotients of representables which are $\lambda$-small; and by Lemma 3.3.1, this implies they are $\lambda$-compact.

We now define $\mathcal{I} \subset \operatorname{Hom}_{\mathcal{E}}$ as the image of $J$ under $i^*$. As $i_*$ preserves monomorphisms and $i^*$ preserves all colimits, $\mathcal{I}$ generates all monomorphisms in $\mathcal{E}$ under pushout, transfinite composition, and retracts. The domains and codomains of morphisms in $\mathcal{I}$ are seen to be $\lambda$-compact by Lemma 3.3.4.

## 4. Main result: a universe satisfying realignment

Let $\mathcal{E}$ be a Grothendieck topos and fix a strongly inaccessible cardinal $\kappa \triangleright \mathfrak{c}(\mathcal{E})$. We have previously shown that $\mathcal{S}_\kappa$ satisfies (U1–7). We construct a new generic map for this class and thereby conclude that $\mathcal{S}_\kappa$ satisfies (U8).

4.1. SATURATION OF SOLVABLE REALIGNMENT PROBLEMS. In Definition 1.1.4 we specified what it means for a universe to have realignment for a class of monomorphisms $\mathcal{M}$. On the other hand, any pullback-stable class of maps $\mathcal{S}$ and morphism $\pi \colon E \longrightarrow U \in \mathcal{S}$ determines a class $\mathcal{J}_\pi$ of monomorphisms along which realignment problems can be solved (regardless of whether $\mathcal{S}$ is a universe and whether $\pi$ is generic).

4.1.1. NOTATION. We will write $\mathcal{J}_\pi$ for the set of all monomorphisms in $\mathcal{E}$ with respect to which $(\mathcal{S}, \pi)$ satisfies the realignment property.

We will establish the closure of $\mathcal{J}_\pi$ under pushout, transfinite composition, and retracts.

4.1.2. LEMMA. The class of realignable monomorphisms $\mathcal{J}_\pi$ is stable under pushout.

PROOF. Fix $A \mapsto B \in \mathcal{J}_\pi$ and a pushout diagram in the following configuration:

$$\begin{array}{c} A \longrightarrow C \\ \updownarrow \\ B \longrightarrow D \end{array} \tag{15}$$