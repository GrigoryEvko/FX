Proof. The left adjoint to $\lrcorner_U = \Omega_U$ is then given by $\exists_U(V, \varphi) = \Sigma_U(V, \varphi) = V$ (proposition 2.3.9).

**Proposition 3.2.6.** Cartesian endomultipliers for pointable objects, are $\top$-slice faithful.

Pointability is not required however: cartesian endomultipliers for unpointable objects may be $\top$-slice faithful (examples 3.3.4 and 3.3.6).

Proof. In this case, $\lrcorner_U = \Omega_U$ and $U \to \top$ is split epi, so this is part of proposition 2.3.10.

Being $\top$-slice full expresses absence of diagonals in the following sense:

**Proposition 3.2.7.** If an endomultiplier for $U$ is both a comonad and $\top$-slice full, then $U$ is a terminal object. If the endomultiplier is moreover cartesian, then it is naturally isomorphic to the identity functor.

Proof. Consider the following diagram:

$$\top \ltimes U \xrightarrow{\top \ltimes \delta} (\top \ltimes U) \ltimes U \tag{14}$$

This is a morphism of slice objects $\top \ltimes \delta : \lrcorner_U \top \to \lrcorner_U(\top \ltimes U)$ and thus, by fullness of $\lrcorner_U$, of the form $\lrcorner_U v$ for some $v : \top \to \top \ltimes U$. This means in particular that

$$\mathrm{id}_{\top \ltimes U} = \pi_1 \circ (\top \ltimes \delta) = \pi_1 \circ (v \ltimes U) = v \circ \pi_1 : \top \ltimes U \to \top \ltimes U. \tag{15}$$

Composing on both sides with $\pi_2 : \top \ltimes U \cong U$, we find that $\mathrm{id}_U = (\pi_2 \circ v) \circ (\pi_1 \circ \pi_2^{-1})$ factors over $\top$, which means exactly that $\pi_2 \circ v : \top \to U$ and $\pi_1 \circ \pi_2^{-1} : U \to \top$ constitute an isomorphism, i.e. $U$ is terminal.

If $\sqcup \ltimes U$ is cartesian, then it is a cartesian product with a terminal object and therefore naturally isomorphic to the identity functor.

### 3.3 Examples

**Example 3.3.1 (Identity).** The identity functor $W \ltimes \top := W$ is an endomultiplier for $\top$.

It is cartesian, $\top$-slice fully faithful, $\top$-slice objectwise pointable iff $\mathcal{W}$ is objectwise pointable and in that case $\top$-slice shard-free, and $\top$-slice right adjoint.

The functor $\lrcorner_\top : \mathcal{W} \to \mathcal{W}/\top : W \mapsto (W, (\,))$ has a left adjoint $\exists_\top : \mathcal{W}/\top \to \mathcal{W} : (W, (\,)) \mapsto W$.

**Example 3.3.2 (Cartesian product).** Let $\mathcal{W}$ be a category with finite products and $U \in \mathcal{W}$.

Then $\sqcup \times U$ is an endomultiplier for $U$.

It is cartesian, $\top$-slice faithful if (but not only if) $U$ is pointable (proposition 3.2.6), $\top$-slice full if and only if $U \cong \top$ (proposition 3.2.7) and $\top$-slice right adjoint (proposition 3.2.5). We do not consider $\top$-slice objectwise pointability for this general case.

The functor $\lrcorner_U = \Omega_U : V \mapsto (V \times U, \pi_2)$ has a left adjoint $\exists_U = \Sigma_U : (W, \psi) \mapsto W$. Hence, we have $\exists_U \lrcorner_U = \sqcup \times U$.

**Example 3.3.3 (Affine cubes).** Let $\square^k$ be the category of affine non-symmetric $k$-ary cubes $\mathbb{I}^n$ as used in [BCH14] (binary) or [BCM15] (unary). A morphism $\varphi : \mathbb{I}^m \to \mathbb{I}^n$ is a function $\sqcup \langle \varphi \rangle : \{i_1, \dots, i_n\} \to \{i_1 \dots i_m, 0, \dots, k-1\}$ such that $i \langle \varphi \rangle = j \langle \varphi \rangle \notin \{0, \dots, k-1\}$ implies $i = j$. We also write $\varphi = (i_1 \langle \varphi \rangle / i_1, \dots, i_n \langle \varphi \rangle / i_n)$. This category is objectwise pointable if and only if $k > 0$.

Consider the functor $\sqcup * \mathbb{I} : \square^k \to \square^k : \mathbb{I}^n \mapsto \mathbb{I}^{n+1}$, which is a multiplier for $\mathbb{I}$. It acts on morphisms $\varphi : \mathbb{I}^m \to \mathbb{I}^n$ by setting $\varphi * \mathbb{I} = (\varphi, i_{m+1} / i_{n+1})$.

It is straightforwardly seen to be copointed, not a comonad, $\top$-slice fully faithful, $\top$-slice objectwise pointable iff $k \neq 0$ and in that case $\top$-slice shard-free, and $\top$-slice right adjoint.

The functor $\lrcorner_\mathbb{I} : \mathbb{I}^n \mapsto (\mathbb{I}^{n+1}, (i_{n+1} / i_1))$ has as left adjoint the functor $\exists_\mathbb{I}$ which sends $(\mathbb{I}^n, \psi)$ to $\mathbb{I}^n$ if $i_1 \langle \psi \rangle \in \{0, \dots, k-1\}$ and to $\mathbb{I}^{n-1}$ (by removing the variable $i_1 \langle \psi \rangle$ and renaming the next ones) otherwise. The action on morphisms is straightforwardly constructed.

11