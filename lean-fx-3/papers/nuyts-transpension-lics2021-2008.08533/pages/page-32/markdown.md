16:32

A. NUYTS AND D. DEVRIESE

Vol. 20:2

Since we can instantiate $\Xi$ with the terminal presheaf $\top \cong \mathbf{y}\top$, we see that each of the presheafwise criteria implies the $\top$-slice criterion from Definition 6.2. Below we give *sufficient* conditions for a multiplier to satisfy the presheafwise criteria:

**Proposition 6.25.** *The multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$ is:*

- *presheafwise faithful if it is $\top$-slice faithful,*
- *presheafwise full if it is $\top$-slice fully faithful,*
- *presheafwise shard-free if it is $\top$-slice full and shard-free,*
- *presheafwise right adjoint if it is $\top$-slice right adjoint.*

*Proof.* See [Nuy20b].

**Example 6.26.** Continuing Example 6.14 about $a$-ary affine cubes, let $\Xi = \mathbf{y}W$. Then $\Xi \ltimes \mathbf{y}(i : \mathbb{I}) \cong \mathbf{y}(W, i : \mathbb{I})$. Pick $(V, \varphi)$ in the category of elements, which is essentially the slice category over $(W, i : \mathbb{I})$, i.e. we view $\varphi$ as a morphism $V \to (W, i : \mathbb{I})$. Then $\varphi$ is directly dimensionally split if $i\langle \varphi \rangle$ is not an endpoint, and in that case $(V, \varphi)$ is isomorphic to $\lrcorner_{\lrcorner_i(\mathbb{I})}^{(yW)}(V', \varphi')$ where $\varphi' : V' \to W$ is obtained by removing $i\langle \varphi \rangle$ and $i$ from the domain and codomain respectively. Thus, there are no direct shards, and the boundary cells are the ones where $i\langle \varphi \rangle$ is an endpoint, i.e. $\mathbf{y}W \ltimes \partial \mathbb{I} \cong \bigoplus_{i=0}^{a-1} \mathbf{y}W$.

**Example 6.27.** Continuing Example 6.13 about $a$-ary *cartesian* cubes, let $\Xi = \mathbf{y}W$. Then $\Xi \ltimes \mathbf{y}(i : \mathbb{I}) \cong \mathbf{y}(W, i : \mathbb{I})$. Pick $(V, \varphi)$ in the category of elements, again we view $\varphi$ as a morphism $V \to (W, i : \mathbb{I})$. Then $\varphi$ is directly dimensionally split if $i\langle \varphi \rangle$ is not an endpoint, *nor equal to $j\langle \varphi \rangle$ for some variable $j$ in $W$, and in that case $(V, \varphi)$ is isomorphic to $\lrcorner_{\lrcorner_i(\mathbb{I})}^{(yW)}(V', \varphi')$ where $\varphi' : V' \to W$ is obtained by removing $i\langle \varphi \rangle$ and $i$ from the domain and codomain respectively. Thus, there are no direct shards, and the boundary cells are the ones where $i\langle \varphi \rangle$ is an endpoint or equal to $j\langle \varphi \rangle$ for some variable in $W$.*

The following (fairly obvious) theorem is paramount to the semantics of transpension elimination (Section 9.3) and the $\Phi$-rule (Section 10.2):

**Theorem 6.28** (Quotient$^{\S A}$ theorem). *If a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$ is $\top$-slice fully faithful and shard-free (hence presheafwise fully faithful and shard-free), then $\lrcorner_{\mathbb{I}}^{(j\Xi)} : \mathcal{W}/\Xi \to \mathcal{W}/(\Xi \ltimes \mathbf{y}U)$ is an equivalence of categories.*

**6.6. MTraS Modalities for multipliers.** We are now well-equipped to study the transpension type in a setting with multiple shape variables.

**Theorem 6.29.** *Any $\top$-slice right adjoint$^{17}$ multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$ and any presheaf $\Xi \in \mathrm{Psh}(\mathcal{W})$ give rise to a quadruple of adjoint functors*

$$\exists_{\mathbf{y}U}^{\Xi} \dashv \lrcorner_{\mathbf{y}U}^{\Xi} \dashv \forall_{\mathbf{y}U}^{\Xi} \dashv \Diamond_{\mathbf{y}U}^{\Xi},$$

$$\exists_{\mathbf{y}U}^{\Xi}, \forall_{\mathbf{y}U}^{\Xi} : \mathrm{Psh}(\mathcal{W}/\Xi \ltimes \mathbf{y}U) \to \mathrm{Psh}(\mathcal{W}/\Xi) \quad \lrcorner_{\mathbf{y}U}^{\Xi}, \Diamond_{\mathbf{y}U}^{\Xi} : \mathrm{Psh}(\mathcal{W}/\Xi) \to \mathrm{Psh}(\mathcal{W}/\Xi \ltimes \mathbf{y}U).$$

*If $\Xi = [\![\mathbb{X}\!]\!]$, the latter three can be internalized as modalities (with an additional left name) $\exists(u : \mathbb{U}) \dashv \lrcorner[u : \mathbb{U}] \dashv \forall(u : \mathbb{U}) \dashv \Diamond[u : \mathbb{U}]$ with*

$$\llbracket \widehat{\blacksquare}_{\lrcorner[u]}^{\exists u} \rrbracket = \exists_{\mathbf{y}U}^{\Xi}, \quad \llbracket \lrcorner[u] \rrbracket = \llbracket \widehat{\blacksquare}_{\forall u}^{\lrcorner[u]} \rrbracket = \lrcorner_{\mathbf{y}U}^{\Xi}, \quad \llbracket \forall u \rrbracket = \llbracket \widehat{\blacksquare}_{\Diamond[u]}^{\forall u} \rrbracket = \forall_{\mathbf{y}U}^{\Xi}, \quad \llbracket \Diamond[u] \rrbracket = \Diamond_{\mathbf{y}U}^{\Xi}.$$

$^{17}$Without $\top$-slice right adjointness, we lose the leftmost adjoint functor $\exists_{\mathbf{y}U}^{\Xi}$ and the leftmost adjoint modality $\lrcorner[u]$.