use the 2-out-of-3 property of weak equivalences between cofibrant-fibrant objects to conclude that $FC \hookrightarrow Y$ is a weak equivalence, and hence a trivial cofibration. Since $F$ is weakly conservative, the map $C \hookrightarrow D$ must be a weak equivalence too. Using that $C$ is bifibrant we can obtain a dashed arrow which is a homotopy inverse of $h$

$$\begin{array}{c} A \xrightarrow{f} C \xrightarrow{Id} C \\ i \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B \xrightarrow{k} D, \end{array}$$

we can take $g := rk$ to be a diagonal filler of the square. Observe that when we apply $F$ to the resulting diagram, it gives us the square and the diagonal in the diagram

$$\begin{array}{c} FA \xrightarrow{Ff} FC \\ Fi \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ FB \xrightarrow{Fk} FD \xrightarrow{\sim} Z \\ \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad u \end{array}$$

where a priori the outer triangle involving $u$ is not commutative. However, we can realize this diagram in the homotopy category $\mathrm{Ho}(FA/\mathcal{N})$. So working in the homotopy category we have $hr = Id$ and $FhFr = Id$. By construction, we also get $Fg = FrFk$, therefore $FhFg = FhFrFk = Fk$ in the homotopy category, and $\rho : FD \xrightarrow{\sim} Z$ becoming an isomorphism implies $vFg = u$ up to homotopy relative to $FA$. $\square$

**Corollary 4.14.** *Let $F : \mathcal{M} \to \mathcal{N}$ a left Quillen functor between weak model categories. Assume that $F : \mathcal{M}^{\mathrm{COF}} \to \mathcal{N}^{\mathrm{COF}}$ is extensible and weakly conservative, then $F$ is a left Quillen equivalence.*

*Proof.* We show directly that $F$ induces an equivalence of categories between the homotopy categories.

Assume that $X \in \mathcal{N}^{\mathrm{COF}}$ is cofibrant. Then we can use that $F$ is extensible for the cofibration $0 \hookrightarrow X$ to obtain a cofibrant object $A \in \mathcal{M}^{\mathrm{COF}}$ and an isomorphism $FA \cong X \in \mathcal{N}$. This shows that the induced functor is essentially surjective.

We now show that for $\mathrm{Ho}(\mathcal{M}) \to \mathrm{Ho}(\mathcal{N})$ is full. Let $B, C \in \mathcal{M}^{\mathrm{COF}}$ cofibrant objects. We could take a fibrant replacement $C^{\mathrm{FIB}}$ and use this instead, so we can freely assume that $C$ is bifibrant. A map $FB \to FC \in$

64