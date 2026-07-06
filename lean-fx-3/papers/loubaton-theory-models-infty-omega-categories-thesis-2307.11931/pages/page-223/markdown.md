4.3. GRAY OPERATIONS

As $C$ is an $(\infty, k)$-category, $\psi$ factors through $C \otimes [1] \to \tau_k^i(C \otimes [1]) \sim C \otimes_k [1]$. We denote by $\phi : C \otimes_k [1] \to C \otimes \{0\}$ the induced morphism. The triple $(i, r, \phi)$ is a left $k$-Gray deformation retract structure. Conversely, $C \otimes \{1\} \to C \otimes [1]$ is a right deformation retract.

One can show similarly that $1 \to 1 \stackrel{co}{\star} C$ is a left $k$-Gray deformation retract, and $1 \to C \star 1$ is a right $k$-Gray deformation retract.

4.3.2.4. The $\infty$-groupoid of left and right Gray retracts enjoys many stability properties:

Proposition 4.3.2.5. Let $(i_a, r_a, \psi_a)$ be a natural family of left (resp. right) $k$-Gray deformation retract structures indexed by an $(\infty, 1)$-category $A$. The triple $(\operatorname{colim}_A i_a, \operatorname{colim}_A r_a, \operatorname{colim}_A \psi_a)$ is a left (resp. right) $k$-Gray deformation retract structure.

Proof. This is an immediate consequence of the fact that $_\otimes_k [1]$ preserves colimits. $\square$

Proposition 4.3.2.6. Suppose that we have a diagram

$$\begin{array}{c} X \xrightarrow{p} Y \xleftarrow{q} Z \\ \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \\ X \xrightarrow{p'} Y' \xleftarrow{q'} Z' \end{array}$$

such that $p \to p'$ and $q \to q'$ are left (resp. right) $k$-Gray deformation retract. The induced square $q^*p \to (q')^*p'$ is a left (resp. right) $k$-Gray deformation retract.

Proof. The proof is an easy diagram chasing. $\square$

Proposition 4.3.2.7. If $p \to p'$ and $p' \to p''$ are two left (resp. right) $k$-Gray deformation retracts, so is $p \to p''$.

Proof. The proof is an easy diagram chasing. $\square$

4.3.2.8. The two following propositions show how the shifting of dimension preserves Gray transformation retract.

Proposition 4.3.2.9. Let $(i : C \to D, r, \psi)$ be a left (resp. right) $(k + 1)$-Gray deformation structure. For any $x : C$ and $y : D$ (resp. $x : D$ and $y : C$), the morphism

$$\begin{array}{c} \hom_C(x, ry) \xrightarrow{i} \hom_D(ix, iry) \xrightarrow{\psi_{y_i}} \hom_D(ix, y) \\ (resp. \hom_C(rx, y) \xrightarrow{i} \hom_D(irx, iy) \xrightarrow{\psi_{x_i}} \hom_D(x, iy)) \end{array}$$

213