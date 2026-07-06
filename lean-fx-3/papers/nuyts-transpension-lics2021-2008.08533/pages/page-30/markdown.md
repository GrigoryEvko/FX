16:30

A. NUYTS AND D. DEVRIESE

Vol. 20:2

which Pinyo and Kraus call the twisted prism functor. A slice object $(V, \varphi)$ is dimensionally split if and only if it is of the form $\varphi = \psi \ltimes I$ (so there are no shards). Hence, all slice objects on the boundary factor over $(((), 0) : () \to () \ltimes \mathbb{I}$ or $(((), 1) : () \to () \ltimes \mathbb{I}$, so that $\partial \mathbb{I} \cong \top \uplus \top$. The multiplier is $\top$-slice right adjoint with

$$\exists_{\mathbb{I}} : \begin{cases} (W, ((), 0)) & \mapsto W^{\text{op}} \\ (W, ((), 1)) & \mapsto W \\ (W \ltimes \mathbb{I}, () \ltimes \mathbb{I}) & \mapsto W, \end{cases} \quad (6.3)$$

with the obvious action on morphisms.

**Example 6.19** (Finite ordinals). In the base category $\omega$ of the topos of trees, used in guarded type theory [BMSS12], where $\text{Hom}(i, j) = \{ * \mid i \leq j \}$, a cartesian product is given by $i \times j = \min(i, j)$. However, this category lacks a terminal object. Instead, on the subcategory $n$ with terminal object $n-1$, which is endowed with the same cartesian product, we consider the multiplier $\sqcup \times i$, which is again an instance of Example 6.11. Any slice object $(j, *)$ (where necessarily $j \leq i$) is dimensionally split with section $*: \min(i, j) = j \to j$; hence there are no shards and $\partial i = \bot$.

**Example 6.20** (Counterexample for $\top$-slice faithful). Let $^2\text{Cube}_{\bot}$ be the category of binary cartesian cubes extended with an initial object. We consider the cartesian product $\sqcup \times \bot$ which sends everything to $\bot$. This is not $\top$-slice faithful, as $\bot_{\bot}$ sends both $(0/i)$ and $(1/i) : () \to (i : \mathbb{I})$ to $[] : (\bot, []) \to (\bot, [])$. It is not $\top$-slice full, as there is no $\psi : () \to \bot$ such that $\psi \times \bot = [] : \bot_{\bot}() \to \bot_{\bot} \bot$.

**6.4. MTraS Modalities for weakening.** Recall that we write $\sqcup \ltimes \mathbf{y}U$ for the left Kan extension of a multiplier $\sqcup \ltimes U$. For any **copointed** multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$ and any presheaf $\Xi \in \text{Psh}(\mathcal{W})$, we get a presheaf morphism $\pi_1 : \Xi \ltimes \mathbf{y}U \to \Xi$. In this situation, the notations in Theorem 5.1 are not very illuminating as they would only mention $\pi_1$ and not $\Xi$ or $U$. Instead, we use the following notations:

**Notation 6.21.** A functor acting on elements:

- $\Sigma_U^{\mathbb{I}} := \Sigma^{\pi_1} : \mathcal{W}/\Xi \ltimes \mathbf{y}U \to \mathcal{W}/\Xi$
- Functors acting on presheaves:
- $\Sigma_{\mathbf{y}U}^{\Xi} := \Sigma^{\pi_1} : \text{Psh}(\mathcal{W}/\Xi \ltimes \mathbf{y}U) \to \text{Psh}(\mathcal{W}/\Xi)$
- $\Omega_{\mathbf{y}U}^{\Xi} := \Omega^{\pi_1} : \text{Psh}(\mathcal{W}/\Xi) \to \text{Psh}(\mathcal{W}/\Xi \ltimes \mathbf{y}U)$
- $\Pi_{\mathbf{y}U}^{\Xi} := \Pi^{\pi_1} : \text{Psh}(\mathcal{W}/\Xi \ltimes \mathbf{y}U) \to \text{Psh}(\mathcal{W}/\Xi)$

Natural transformations:

$$\begin{aligned} \text{copy}_{\mathbf{y}U}^{\Xi} &:= \text{copy}^{\pi_1} : 1 \to \Omega_{\mathbf{y}U}^{\Xi} \circ \Sigma_{\mathbf{y}U}^{\Xi} & \quad \text{drop}_{\mathbf{y}U}^{\Xi} &:= \text{drop}^{\pi_1} : \Sigma_{\mathbf{y}U}^{\Xi} \circ \Omega_{\mathbf{y}U}^{\Xi} &\to 1 \\ \text{const}_{\mathbf{y}U}^{\Xi} &:= \text{const}^{\pi_1} : 1 \to \Pi_{\mathbf{y}U}^{\Xi} \circ \Omega_{\mathbf{y}U}^{\Xi} & \quad \text{app}_{\mathbf{y}U}^{\Xi} &:= \text{app}^{\pi_1} : \Omega_{\mathbf{y}U}^{\Xi} \circ \Pi_{\mathbf{y}U}^{\Xi} &\to 1 \end{aligned}$$

For modalities, we use the weakening notations already introduced in Notation 5.3: for $\Xi = [\![\mathbb{X}\!]\!]$, we internalize the above functors as $\Sigma(u : \mathbb{U}) \dashv \Omega[u : \mathbb{U}] : \mathbb{X} \to (\mathbb{X}, u : \mathbb{U})$ and $\Pi(u : \mathbb{U}) : (\mathbb{X}, u : \mathbb{U}) \to \mathbb{X}$, sometimes abbreviating to $\Sigma u \dashv \Omega[u]$ and $\Pi u$, and the above natural transformations as $\text{drop}_u \dashv \text{const}_u$ and $\text{copy}_u \dashv \text{app}_u$.