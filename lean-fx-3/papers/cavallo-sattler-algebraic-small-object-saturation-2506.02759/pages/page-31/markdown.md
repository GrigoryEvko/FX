**Definition 3.3.1.** A *notion of composable structure* on a category $\mathcal{E}$ is a double functor $U: \mathbb{A} \to \operatorname{Sq}(\mathcal{E})$ from a pseudo double category $\mathbb{A}$ such that $U_0: \mathbb{A}_0 \to \mathcal{E}$ is an identity (in particular $\mathbb{A}_0 = \mathcal{E}$) and $U^\downarrow: \mathbb{A}^\downarrow \to \mathcal{E}^\rightarrow$ is a conservative isofibration.

**Notation 3.3.2.** Following Bourke and Garner, when we write a vertical morphism in a notion of composable structure $U: \mathbb{A} \to \operatorname{Sq}(\mathcal{E})$ in boldface, *e.g.* $\boldsymbol{f}: A \leftrightarrow B$, we implicitly bind the same letter without boldface to its underlying morphism, *e.g.* using $f: A \to B$ for $U\boldsymbol{f}$.

**Proposition 3.3.3.** For any AWFS $(\mathsf{L}, \mathsf{R})$ on a category $\mathcal{E}$, the projections $\mathsf{L}$-$\operatorname{Coalg} \to \operatorname{Sq}(\mathcal{E})$ and $\mathsf{L}_\mathsf{p}$-$\operatorname{Coalg} \to \operatorname{Sq}(\mathcal{E})$ are notions of composable structure. $\square$

**Definition 3.3.4** ([BG16a, §3.5] or [BG16b, §2.5]). A pseudo double category $\mathbb{A}$ is *left-connected* when $\mathbf{id}: \mathbb{A}_0 \to \mathbb{A}^\downarrow$ is left adjoint to $\operatorname{dom}_\downarrow: \mathbb{A}^\downarrow \to \mathbb{A}_0$. In this case, the counit $\Delta: \mathbf{id} \circ \operatorname{dom}_\downarrow \to \operatorname{Id}$ at $\boldsymbol{f}: A \leftrightarrow B$ defines a square

$$\begin{array}{c} A \xlongequal{\quad} A \\ \mathbf{id} \downarrow \quad \Delta \quad \downarrow \boldsymbol{f} \\ A \dashrightarrow B \end{array} \tag{3.2}$$

which we call a *left connection*.

Any left-connected pseudo double category $\mathbb{A}$ induces a double functor $\mathbb{A} \to \operatorname{Sq}(\mathbb{A}_0)$ which is the identity on horizontal morphisms and sends $\boldsymbol{f}: A \leftrightarrow B$ to the dashed morphism of (3.2) [BG16a, §3.5]. We say that a notion of composable structure $U: \mathbb{A} \to \operatorname{Sq}(\mathcal{E})$ is *left-connected* when $\mathbb{A}$ is left-connected and $U$ is the double functor induced by the left connection.

**Proposition 3.3.5** (see [BG16a, Theorem 6(ii)]). For any AWFS $(\mathsf{L}, \mathsf{R})$ on $\mathcal{E}$, the notions of composable structure $U_\mathsf{L}: \mathsf{L}$-$\operatorname{Coalg} \to \operatorname{Sq}(\mathcal{E})$ and $U_{\mathsf{L}_\mathsf{p}}: \mathsf{L}_\mathsf{p}$-$\operatorname{Coalg} \to \operatorname{Sq}(\mathcal{E})$ are left-connected. $\square$

**Notation 3.3.6.** When $U: \mathbb{A} \to \operatorname{Sq}(\mathcal{E})$ is a notion of composable structure and $\mathcal{M}, \mathcal{N}$ are wide subcategories of $\mathcal{E}$, write $\mathbb{A}^\downarrow(\frac{\mathcal{M}}{\mathcal{N}})$ for the wide subcategory of $\mathbb{A}^\downarrow$ given by the pullback

$$\begin{array}{c} \mathbb{A}^\downarrow(\frac{\mathcal{M}}{\mathcal{N}}) \longmapsto \mathbb{A}^\downarrow \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathcal{E}^\rightarrow(\frac{\mathcal{M}}{\mathcal{N}}) \longmapsto \mathcal{E}^\rightarrow. \end{array}$$

**Definition 3.3.7.** Let $\mathcal{M}$ be a $\kappa$-backdrop in a category $\mathcal{E}$. A notion of composable structure $U: \mathbb{A} \to \operatorname{Sq}(\mathcal{E})$ is $(\kappa, \mathcal{M})$-*cellular* if

- (a) $(1 + \alpha)$-chains in $\mathbb{A}^\downarrow(\frac{\cong}{\mathcal{M}})$ have colimits in $\mathbb{A}^\downarrow$ for $\alpha \preceq \kappa$ and $U^\downarrow$ preserves these;
- (b) $\mathbb{A}^\downarrow(\frac{\cong}{\mathcal{M}})$ is closed under cobase change in $\mathbb{A}^\downarrow$ and $U^\downarrow$ preserves these pushouts.

Equivalently, $U$ is $(\kappa, \mathcal{M})$-cellular when $\mathbb{A}^\downarrow(\frac{\cong}{\mathcal{M}})$ is a $\kappa$-backdrop in $\mathbb{A}^\downarrow$ and $U^\downarrow$ is a $\kappa$-backdrop-preserving functor $(\mathbb{A}^\downarrow, \mathbb{A}^\downarrow(\frac{\cong}{\mathcal{M}})) \longrightarrow (\mathcal{E}^\rightarrow, \mathcal{E}^\rightarrow(\frac{\cong}{\mathcal{M}}))$.

**Proposition 3.3.8.** For any AWFS $(\mathsf{L}, \mathsf{R})$ on a category $\mathcal{E}$, the notions of composable structure $U_\mathsf{L}: \mathsf{L}$-$\operatorname{Coalg} \to \operatorname{Sq}(\mathcal{E})$ and $U_{\mathsf{L}_\mathsf{p}}: \mathsf{L}_\mathsf{p}$-$\operatorname{Coalg} \to \operatorname{Sq}(\mathcal{E})$ are $(\kappa, \mathcal{M})$-cellular for every limit ordinal $\kappa > 0$ and $\kappa$-backdrop $\mathcal{M}$.

*Proof.* The forgetful functors associated to a comonad or copointed endofunctor create *any* colimits existing in the base category. See, *e.g.*, Borceux [Bor94, Proposition 4.3.1] for the (co)monad case; the (co)pointed endofunctor case goes by the same argument. $\square$

31