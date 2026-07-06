The reason why we isolate the two properties in the definition above is because the first one is well-behaved with respect to the language we constructed, see theorem 4.15. In theorem 4.14, we justify the “trivial” part of theorem 4.11 by showing that an extensible and weakly conservative left Quillen functor is a left Quillen equivalence, to do this we need an intermediate result.

**Lemma 4.13.** *Let be $F : \mathcal{M} \to \mathcal{N}$ a left Quillen functor which is extensible and weakly conservative. Suppose there are diagrams*

$$\begin{array}{c c} A \xrightarrow{f} C & FA \xrightarrow{Ff} FC \\ i \Big\downarrow & Fi \Big\downarrow \qquad v \Big\downarrow \sim \\ B & FB \xrightarrow{u} Z \end{array}$$

in $\mathcal{M}$ and $\mathcal{N}$, respectively, where $C \in \mathcal{M}^{\mathrm{BIF}}$ and $Z \in \mathcal{N}^{\mathrm{BIF}}$ are bifibrant and the right square is commutative. Then, there exists $g : B \to C$ that makes the triangle commutative and such that in the diagram

$$\begin{array}{c} FA \xrightarrow{Ff} FC \\ Fi \Big\downarrow \qquad \nearrow Fg \nearrow v \Big\downarrow \sim \\ FB \xrightarrow{u} Z \end{array}$$

the lower triangle commutes up to homotopy relative to $FA$.

*Proof.* Since $F$ is left Quillen then we have $F(B \coprod_A C) \cong FB \coprod_{FA} FC$ and is cofibrant. Up to this isomorphism, we factor the map $F(B \coprod_A C) \to Z$ as $F(B \coprod_A C) \hookrightarrow Y \xrightarrow{\sim} Z$. Since $F$ is extensible we can lift this cofibration to a cofibration $B \coprod_A C \hookrightarrow D$ together with the isomorphism $FD \cong Y$ making the resulting triangle commutative, which also implies that $FD$ is bifibrant since $Y$ is. Furthermore, this produces a commutative diagram as on the left,

$$\begin{array}{c c c} A \xrightarrow{f} C & FC \xrightarrow{\sim} Z \\ i \Big\downarrow & \Big\downarrow \searrow & \searrow \\ B \xrightarrow{} B \coprod_A C \xrightarrow{h} F & FD \xrightarrow{\sim} Y \\ k & \searrow \searrow & \searrow \\ & D \end{array}$$

while the diagram on the right is the result of applying $F$, we introduce the name $\rho : FD \xrightarrow{\sim} Z$ for the evident resulting trivial fibration. We can

63