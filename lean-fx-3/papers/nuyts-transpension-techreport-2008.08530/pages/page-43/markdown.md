where \(\Omega^{\nu_1^{-1}}\) is the strict inverse to \(\Omega^{\nu_1}\).

Then we have \(\Sigma^{\prime \nu_1^{-1}}\mathbb{J}_{U'}^{\prime G_1\Psi}G / \Psi \cong F / \Psi \ltimes U\mathbb{J}_U^{\prime \Psi}\). This yields the following commutation table:

|   | \( F_{!},G_{!} \) | \( F^{*},G^{*} \) | \( F_{*},G_{*} \)  |
| --- | --- | --- | --- |
|  \( \exists \) | \( \exists_{\mathbf{y}U}^{G_{!}\Psi}\Omega^{\nu_{1}^{-1}}|F_{!}^{\Psi\ltimes\mathbf{y}U}| \triangleright_{1}G_{!}^{\Psi}\exists_{\mathbf{y}U}^{\Psi}| \) | \( \exists_{\mathbf{y}U}^{\Psi}|F^{\Psi*}\triangleright_{2}G^{\Psi*}\exists_{\mathbf{y}U'}^{G_{!}\Psi}\Omega^{\nu_{1}^{-1}}| \) |   |
|  \( \bot \) | \( \Omega^{\nu_{1}}|\exists_{\mathbf{y}U'}^{G_{!}\Psi}G_{!}^{\Psi}\cong F_{!}^{\Psi\ltimes\mathbf{y}U}| \exists_{\mathbf{y}U}^{\Psi}| \) | \( \exists_{\mathbf{y}U}^{\Psi}|G^{\Psi*}\triangleright_{1}F^{\Psi\ltimes\mathbf{y}U*}\Omega^{\nu_{1}}|\exists_{\mathbf{y}U'}^{G_{!}\Psi}| \) | \( \Omega^{\nu_{1}}|\exists_{\mathbf{y}U'}^{G_{!}\Psi}G_{*}^{\Psi}\triangleright_{2}F_{*}^{\Psi\ltimes\mathbf{y}U}| \exists_{\mathbf{y}U}^{\Psi}| \)  |
|  \( \forall \) | \( \forall_{\mathbf{y}U'}^{G_{!}\Psi}\Omega^{\nu_{1}^{-1}}|F_{!}^{\Psi\ltimes\mathbf{y}U}| \leftarrow G_{!}^{\Psi}\forall_{\mathbf{y}U}^{\Psi}| \) | \( \forall_{\mathbf{y}U}^{\Psi}|F^{\Psi*}\cong G^{\Psi*}\forall_{\mathbf{y}U'}^{G_{!}\Psi}\Omega^{\nu_{1}^{-1}}| \) | \( \forall_{\mathbf{y}U'}^{G_{!}\Psi}\Omega^{\nu_{1}^{-1}}|F_{*}^{\Psi\ltimes\mathbf{y}U}| \triangleright_{1}G_{*}^{\Psi}\forall_{\mathbf{y}U}^{\Psi}| \)  |
|  \( \Diamond \) |  | \( \Diamond_{\mathbf{y}U}^{\Psi}|G^{\Psi*}\leftarrow F^{\Psi\ltimes\mathbf{y}U*}\Omega^{\nu_{1}}|\Diamond_{\mathbf{y}U'}^{G_{!}\Psi}| \) | \( \Omega^{\nu_{1}}|\Diamond_{\mathbf{y}U'}^{G_{!}\Psi}G_{*}^{\Psi}\cong F_{*}^{\Psi\ltimes\mathbf{y}U}| \Diamond_{\mathbf{y}U}^{\Psi}| \)  |

where any statement holds if the mentioned functors exist, and where

1. In general, \(\triangleright_{1}\) means \(\rightarrow\) and \(\triangleright_{2}\) means nothing.
2. If \(\mathcal{W} = \mathcal{V}\), \(\mathcal{W}' = \mathcal{V}'\), \(F = G\), both multipliers are cartesian and \(\nu\) respects the first projection, i.e. \(\pi_1 \circ \nu = G\pi_1\), then \(\triangleright_1\) upgrades to \(\cong\) and \(\triangleright_2\) upgrades to \(\rightarrow\). Note that in this case we have \(GU \cong G(\top \times U) \cong_{\nu} G\top \times U'\).

Remark 6.4.2. In the above theorem, we think of \( F \) and \( G \) as similar functors; if we are dealing with endomultipliers, we will typically take \( F = G \). The multipliers, however, will typically be different, as in general \( U \not\cong FU \).

Proof. Since \(\nu_{!}\) is an isomorphism, \(\Sigma^{\prime \nu_{!}}\) is a strictly invertible functor with inverse \(\Sigma^{\prime \nu_{1}^{-1}}\). Since \(\sqcup^{*}\) is a 2-functor, \(\Omega^{\nu_{1}}\) is also strictly invertible with inverse \(\Omega^{\nu_{1}^{-1}}\). Because equivalences of categories are adjoint to their inverse, we get the chains of isomorphisms displayed.

1. The given commutation property in the base category follows immediately from the definitions and naturality of \(\nu\) and its image under \(\sqcup_{!}\). The rest of the table then follows by lemma 2.1.2.
2. We invoke theorem 6.2.1 with \(\sigma = \pi_2: \Psi \times \mathbf{y}U \to \Psi\). This yields \(\Omega_{\mathbf{y}U}^{\Psi}|G^{\Psi*} = G^{\Psi \times \mathbf{y}U*}\Omega^{G_1\pi_2|}\). Now \(G_1\pi_2 = \pi_2 \circ \nu_1\) so we can rewrite this to \(\Omega_{\mathbf{y}U}^{\Psi}|G^{\Psi*} = G^{\Psi \times \mathbf{y}U*}\Omega^{\nu_1|}\Omega_{\mathbf{y}U'}^{G_1\Psi|}\). The rest of the table then follows by lemma 2.1.2.

### 6.5 Multiplier and multiplier

Theorem 6.5.1. Assume we have a commutative diagram (up to natural isomorphism \(\nu : \sqcup \ltimes U \ltimes I \cong \sqcup \ltimes J \ltimes U'\)) of multipliers

\[
\begin{array}{c} \mathcal {W} \xrightarrow {\sqcup \ltimes J} \mathcal {W} ^ {\prime} \\ \sqcup \ltimes U \Bigg | _ {\downarrow} \quad \Bigg | _ {\sqcup \ltimes U ^ {\prime}} \\ \mathcal {V} \xrightarrow {\sqcup \ltimes I} \mathcal {V} ^ {\prime}. \end{array} \tag {58}
\]

Then we have the commutation table given in fig. 1 where every statement holds if the mentioned functors exist, and where

1. In general, \(\triangleright_{1}\) means \(\rightarrow\), \(\triangleleft^{1}\) means \(\leftarrow\) and the other symbols mean nothing.
2. If \(\mathcal{W} = \mathcal{W}'\), \(\mathcal{V} = \mathcal{V}'\), \(\sqcup \ltimes U = \sqcup \ltimes U'\), the multipliers \(\sqcup \ltimes J\) and \(\sqcup \ltimes I\) are cartesian and \((\pi_1 \ltimes U) \circ \nu = \pi_1 : (\sqcup \ltimes U) \times I \to \sqcup \ltimes U\), then \(\triangleleft^1\) upgrades to \(\cong\) and \(\triangleleft^2\) upgrades to \(\leftarrow\).

(a) If moreover \(\sqcup \ltimes U\) is \(\top\)-slice fully faithful, then \(\triangleleft^2\) upgrades to \(\cong\) and \(\triangleleft^3\) upgrades to \(\leftarrow\).

3. The symbols \(\triangleright_{i}\) upgrade under symmetric conditions.

Proof. 1. In the base category, it is clear that \(\mathbb{J}_{U'}^{\prime \Psi \ltimes \mathbf{y}J}\mathbb{J}_{J}^{\prime \Psi}\cong \Sigma^{\prime \nu_{1}}\mathbb{J}_{I}^{\prime \Psi \ltimes \mathbf{y}U}\mathbb{J}_{U}^{\prime \Psi}\). Applying the 2-functor \(\sqcup^{*}\) yields the commutation law for \(\forall\) and hence, by lemma 2.1.2, the general case.

43