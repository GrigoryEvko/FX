we can take the transpose of $\omega_1$ as a first component and $\chi_2$ as a second component of the transpose of $(\omega_1, \omega_2)$. It remains to show that these form a commutative diagram with $\psi : W_1 \to W_2$ and $\varphi \circ \pi_1 : V_1 \ltimes U \to V_2$. But we have a commutative diagram

$$\begin{array}{c} W_1 \xlongequal{\quad} \Sigma_U(W_1, \psi_1) \xrightarrow{\quad \Sigma_U \text{copy}_U \quad} \Sigma_U \lrcorner \\ \Bigg\downarrow \quad \Bigg\downarrow_{\text{hide}_U} \quad \Bigg\downarrow_{\text{hide}_U} \quad \Bigg\downarrow_{\text{hide}_U} \quad \Bigg\downarrow_{\pi_1} \\ \exists_U(W_1, \psi_1) \xrightarrow{\quad \exists_U \text{copy}_U \quad} \exists_U \lrcorner \\ \Bigg\downarrow \quad \Bigg\downarrow_{\text{hide}_U} \quad \Bigg\downarrow_{\text{hide}_U} \quad \Bigg\downarrow_{\text{hide}_U} \quad \Bigg\downarrow_{\pi_1} \\ W_1 \xrightarrow{\quad \text{hide}_U \quad} \exists_U(W_1, \psi_1) \xrightarrow{\quad \omega_1 \quad} \quad V_1 \end{array}$$

which can be pasted on top of the previous one to settle the matter. Finally, it is surprisingly easy to verify that the transposition operations just defined are mutually inverse.

**Example 3.3.11** (Depth $d$ cubes). Let $\square_d$ with $d \geq -1$ be the category of depth $d$ cubes, used as a base category in degrees of relatedness [ND18, Nuy18].$^{11}$ Its objects take the form $(i_1 : (\lrcorner k_1), \dots, i_n : (\lrcorner k_n))$ where all $k_j \in \{0, \dots, d\}$. Conceptually, we have a map $(\lrcorner k) \to (\lrcorner \ell)$ if $k \geq \ell$. Thus, morphisms $\varphi : (i_1 : (\lrcorner k_1), \dots, i_n : (\lrcorner k_n)) \to (j_1 : (\lrcorner \ell_1), \dots, j_m : (\lrcorner \ell_m))$ send every variable $j : (\lrcorner \ell)$ of the codomain to a value $j \langle \varphi \rangle$, which is either 0, 1 or a variable $i : (\lrcorner k)$ of the domain such that $k \geq \ell$. The terminal object is () and the category is objectwise pointable.

Consider in this category the functor $\sqcup \times (i : (\lrcorner k)) : \square_d \to \square_d : W \mapsto (W, i : (\lrcorner k))$, which is an endomultiplier for $(i : (\lrcorner k))$.

It is cartesian (hence $\top$-slice non-full and right adjoint with $\exists_{(i: (\lrcorner k))(W, \psi)} = W$), $\top$-slice faithful, objectwise pointable and shard-free.

**Example 3.3.12** (Erasure). Let $\text{Erase}_d = \{\top \leftarrow 0 \leftarrow 1 \leftarrow \dots \leftarrow d\}$ with $d \geq -1$. This category has cartesian products $m \times n = \max(m, n)$ and only the terminal object is pointable. We remark that $\widetilde{\text{Erase}}_0$ is the Sierpiński topos.

We consider the endomultiplier $\sqcup \times i : \text{Erase}_d \to \text{Erase}_d$.

It is cartesian (hence $\top$-slice non-full and right adjoint with $\exists_i(j, \psi) = j$), $\top$-slice faithful and not $\top$-slice objectwise pointable.

We believe that this base category is a good foundation for studying the semantics of erasure of irrelevant subterms in Degrees of Relatedness [ND18]. The idea is that, for a presheaf $\Gamma$, the set $\top \Rightarrow \Gamma$ is the set of elements, whereas the set $i \Rightarrow \Gamma$ is the set of elements considered up to $i$-relatedness, but also whose existence is only guaranteed by a derivation up to $i$-relatedness.

**Example 3.3.13** (Counterexample for $\top$-slice faithful). Let $\square_\perp^2$ be the category of binary cartesian cubes extended with an initial object. We consider the cartesian product $\sqcup \times \perp$ which sends everything to $\perp$. This is not $\top$-slice faithful, as $\lrcorner \perp$ sends both $(0/i)$ and $(1/i) : () \to (i : \mathbb{I})$ to $[] : (\perp, []) \to (\perp, [])$. It is not $\top$-slice full, as there is no $\psi : () \to \perp$ such that $\psi \times \perp = [] : \lrcorner \perp() \to \lrcorner \perp\perp$.

## 3.4 Properties

### 3.4.1 Functoriality

**Definition 3.4.1.** A multiplier morphism or morphism multiplier for $\upsilon : U \to U'$ is a natural transformation $\sqcup \ltimes \upsilon : \sqcup \ltimes U \to \sqcup \ltimes U'$ such that $\pi_2 \circ (\top \ltimes \upsilon) \circ \pi_2^{-1} = \upsilon : U \to U'$ (or equivalently $\pi_2 \circ (W \ltimes \upsilon) = \upsilon \circ \pi_2 : W \ltimes U \to U'$ for all $W$).

- If both multipliers are copointed, then $\upsilon$ is said to be a morphism of copointed multipliers$^{1A}$ if it is a morphism of copointed endofunctors, i.e. if $\pi_1 \circ (W \ltimes \upsilon) = \pi_1$,

$^{11}$For $d = -1$, we get the point category. For $d = 0$, we get the category of binary cartesian cubes $\square^2$. For $d = 1$, we get the category of bridge/path cubes [NVD17, Nuy18].

15