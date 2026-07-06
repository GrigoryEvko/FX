5.2. CARTESIAN FIBRATIONS

**Proposition 5.2.1.12.** Let $p : X \to C$ be a morphism, and $x, y$ two objects of $X$. Then, if $p$ is a right (resp. left) cartesian fibration, the induced morphism $p : \hom_X(x, y) \to \hom_C(x, y)$ is a left (resp. right) cartesian fibration.

*Proof.* This is a direct consequence of proposition 5.2.1.8.

**Proposition 5.2.1.13.** Consider a cocartesian square

$$
\begin{array}{c}
X'' \xrightarrow{j} X' \longrightarrow X \\
p'' \downarrow \quad \downarrow \quad p' \downarrow \quad \downarrow \quad p \downarrow \\
Y'' \xrightarrow{i} Y' \longrightarrow Y
\end{array}
$$

If $p$ is a left (resp. right) cartesian fibration and $i$ is a right (resp. left) Gray deformation retract, then $p'' \to p'$ is a right (resp. left) Gray deformation retract. Moreover, this left (resp. right) Gray deformation retract structure is functorial in $p$.

Similarly, if $p$ is a left (resp. right) cartesian fibration and $i$ is a right (resp. left) deformation retract, then $p'' \to p'$ is a right (resp. left) deformation retract. This left (resp. right) deformation retract structure is functorial in $p$.

*Proof.* We suppose that $p$ is a right cartesian fibration. By stability under pullbacks, so is $p'$. Let $(i : C \to D, r, \phi)$ be a left Gray deformation retract structure. We define the morphism $\psi$ as the lift of the following commutative square:

$$
\begin{array}{c}
X'' \otimes [1]^{\sharp} \cup X' \otimes \{0\} \xrightarrow{(X'' \otimes \mathbb{I}) \cup id} X' \\
\downarrow \quad \downarrow \quad \psi \quad \downarrow p' \\
X' \otimes [1]^{\sharp} \xrightarrow{} Y'' \otimes [1]^{\sharp} \longrightarrow Y'
\end{array}
$$

Remark that the restriction of $\psi$ to $X' \otimes \{1\}$ factors through $X''$ and then defines a retract $s : Y \to X$ of $j$. This provides a right Gray deformation structure for $p \to p''$. We proceed similarly for the dual case.

The functoriality of the Gray deformation retract structure comes from the fact that only functorial operations were used. Indeed, pullbacks, pushouts and the Gray tensor product are functorial. The formation of the lift $\psi$ is also functorial according to proposition 4.1.2.11.

To verify the second claim, one may utilize the same proof, exchanging $\otimes$ with $\times$. $\square$

**Corollary 5.2.1.14.** Let $p : X \to B^{\sharp}$ and $q : Y \to B^{\sharp}$ be two left cartesian fibrations and $\phi : p \to q$ a morphism over $B^{\sharp}$. The morphism $\phi$ is an equivalence if and only if, for any object $b$ of $B$, the induced morphism $\{b\}^*\phi : \{b\}^*X \to \{b\}^*Y$ is an equivalence.

261