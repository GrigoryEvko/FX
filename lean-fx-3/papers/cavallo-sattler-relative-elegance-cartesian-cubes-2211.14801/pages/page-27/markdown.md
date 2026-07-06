Relative Elegance and Cartesian Cubes with One Connection

27

weak factorization systems [GT06; Gar09] for the sake of concision, but these form the conceptual backbone of Gambino and Sattler's results.

Definition 4.10 (Uniform lifting) Let $u: \mathbf{I} \to \mathbf{E}^{\rightarrow}$ be a functor. A right $u$-map is a map $f: Y \to X$ in $\mathbf{E}$ equipped with

- for each $i \in \mathbf{I}$ and filling problem

$$\begin{array}{c} A_{i} \xrightarrow{h} Y \\ u_{i} \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B_{i} \xrightarrow{k} X, \end{array}$$

a diagonal filler $\varphi(i, h, k): B_{i} \to Y$;

- such that for each $\alpha: j \to i$ and diagram

$$\begin{array}{c} A_{j} \xrightarrow{a} A_{i} \xrightarrow{h} Y \\ u_{j} \Big\downarrow \qquad u_{\alpha} \qquad \Big\downarrow u_{i} \qquad \Big\downarrow f \\ B_{j} \xrightarrow{b} B_{i} \xrightarrow{k} X, \end{array}$$

we have $\varphi(i, h, k)b = \varphi(j, ha, kb)$.

When $u$ is a subcategory inclusion, we may instead say that $f$ is a right $\mathbf{I}$-map.

Notation 4.11 Given a category $\mathbf{E}$, write $\mathbf{E}_{\text{cart}}^{\rightarrow} \subseteq \mathbf{E}^{\rightarrow}$ for the category of arrows in $\mathbf{E}$ and cartesian squares between them.

Write $\mathcal{M}$ for the full subcategory of $\mathrm{PSh}_{\kappa}(\square_{\vee})_{\text{cart}}^{\rightarrow}$ consisting of monomorphisms.

Definition 4.12 We say a map in $\mathrm{PSh}_{\kappa}(\square_{\vee})_{\text{cart}}^{\rightarrow}$ is a uniform trivial fibration when it is a right $\mathcal{M}$-map.

Remark 4.13 If working constructively, one must replace $\mathcal{M}$ with the full subcategory $\mathcal{M}_{\text{dec}}$ of levelwise decidable monomorphisms, i.e., those $m: A \mapsto B$ such that $m_I$ is isomorphic to a coproduct inclusion for all $I \in \square_{\vee}$. This restriction is used (see e.g., Orton and Pitts [OP18, Theorem 8.4]) in the proof of the realignment property, which is important to the construction of fibrant universes.

The following proposition lets us characterize the trivial fibrations (and later, the fibrations) as the maps with uniform right lifting against a small category.

Proposition 4.14 (GS17, Proposition 5.16) Let $\mathbf{C}$ be a small category and $\mathbf{I}$ be a full subcategory of $\mathrm{PSh}(\mathbf{C})_{\text{cart}}^{\rightarrow}$ closed under base change to representables, i.e., such that $x^* f \in \mathbf{I}$ for any $f: Y \to X$ in $\mathbf{I}$ and $x: \not\perp a \to X$. Write $\mathbf{I}^{\not\perp}$ for the full subcategory of $\mathbf{I}$ consisting of maps with representable codomain. Then a map in $\mathrm{PSh}(\mathbf{C})$ is a right $\mathbf{I}$-map if and only if it is a right $\mathbf{I}^{\not\perp}$-map.

2025/10/16 00:43