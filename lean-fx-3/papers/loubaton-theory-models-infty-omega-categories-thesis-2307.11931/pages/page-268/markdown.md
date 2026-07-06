CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

## 5.2 Cartesian fibrations

### 5.2.1 Left and right cartesian fibrations

**5.2.1.1.** We denote by I the set of morphisms of shape $X \otimes \{0\} \to X \otimes [1]^\sharp$ for $X$ being either $\mathbf{D}_n^b$ or $(\mathbf{D}_n)_t$. A morphism is *initial* if it is in $\widehat{\mathbf{I}}$. Conversely, we denote by F the set of morphisms of shape $X \otimes \{1\} \to X \otimes [1]^\sharp$ for $X$ being either $\mathbf{D}_n^b$ or $(\mathbf{D}_n)_t$. A morphism is *final* if it is in $\widehat{\mathbf{F}}$.

Initial and final morphisms are stable under colimits, retract, composition and left cancellation according to the result of section 4.1.2.

The proposition 5.1.3.3 implies that the full duality $(\_)^\circ$ sends final (resp. initial) morphisms to initial (resp. final) morphisms.

**Example 5.2.1.2.** By stability of initial and final morphisms by colimits, for any marked $(\infty, \omega)$-category $C$, $C \otimes \{0\} \to C \otimes [1]^\sharp$ is initial, and $C \otimes \{1\} \to C \otimes [1]^\sharp$ is final.

**Proposition 5.2.1.3.** *Left Gray deformation retracts (resp. left deformation retract) are initial and right Gray deformation retracts (resp. right deformation retract) are final.*

*Proof.* Let $i : C \to D$ be a left Gray deformation retract. The diagram

$$\begin{array}{ccc} C & \xrightarrow{i} & D \otimes \{0\} & \xrightarrow{r} & C \\ i \downarrow & & \downarrow & & \downarrow \\ D \otimes \{1\} & \longrightarrow & D \otimes [1]^\sharp & \xrightarrow{\psi} & D \end{array}$$

expresses $i$ as a retract of $D \otimes \{0\} \to D \otimes [1]^\sharp$, which is an initial morphism according to example 5.2.1.2. The morphism $i$ is then initial.

As left deformation retracts are left Gray deformation retracts, they are initial. The case of right (Gray) deformation retracts follows by duality. $\square$

**Corollary 5.2.1.4.** *Let $a$ be a globular sum of dimension $(n+1)$. We denote by $s_n(a)$ and $t_n(a)$ the globular sum defined in 1.1.2.12. If $n$ is even, $s_n(a)^b \to a^{\sharp n}$ is initial, and $t_n(a)^b \to a^{\sharp n}$ is final. Dually, if $n$ is odd, $t_n(a)^b \to a^{\sharp n}$ is initial, and $s_n(a)^b \to a^{\sharp n}$ is final*
*Proof.* This is a direct consequence of propositions 5.1.4.11 and 5.2.1.3. $\square$

**Proposition 5.2.1.5.** *For any $n$, the morphism $\mathbb{I}_n : (\mathbf{D}_{n+1})_t \to \mathbf{D}_n^b$ is both initial and final.*

*Proof.* According to lemma 5.2.1.4 there exists $\alpha \in \{-, +\}$ such that $i_n^\alpha : (\mathbf{D}_n)^b \to (\mathbf{D}_{n+1})_t$ is initial. As $\mathbb{I}_n$ is a retraction of this morphism, and as initial morphisms are closed under left cancellation according to proposition 4.1.2.3, $\mathbb{I}_n$ is initial. The second case follows by duality. $\square$

258