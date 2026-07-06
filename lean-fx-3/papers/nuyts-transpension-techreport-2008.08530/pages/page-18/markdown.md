**Theorem 3.4.10** ($\top$-slice quotient theorem$^{\S A}$). If a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice fully faithful and shard-free, then $\exists_U : \mathcal{W} \simeq \mathcal{V} // U$ is an equivalence of categories. $\square$

**Example 3.4.11** (Identity). In the category $\mathcal{W}$ with the identity multiplier $W \ltimes \top = W$, every morphism $W \to \top$ is dimensionally split with $\mathrm{id}_W$ as an invertible dimensional section. The multiplier is $\top$-slice fully faithful and shard-free, so the quotient theorem applies.

**Example 3.4.12** (Nullary cubes). In the categories of $k$-affine cubes $\square^k$ (example 3.3.3) and $k$-ary cartesian cubes $\square^k$ (example 3.3.4) ($k \geq 0$), a morphism $\varphi : \mathbb{I}^n \to \mathbb{I}$ is dimensionally split if $i_1 \langle \varphi \rangle$ is a variable. The multipliers $\sqcup * \mathbb{I} : \square^k \to \square^k$ and $\sqcup \times \mathbb{I} : \square^k \to \square^k$ are $\top$-slice shard-free. The multiplier for affine cubes is also $\top$-slice fully faithful so the quotient theorem applies.

**Example 3.4.13** (Clocks). In the category of clocks $\odot$ (example 3.3.6), a morphism $\varphi : V \to (i : \odot_k)$ is dimensionally split if $i \langle \varphi \rangle$ has clock type $\odot_k$. The multiplier $\sqcup \times (i : \odot_k)$ is $\top$-slice fully faithful and shard-free, so the quotient theorem applies.

**Example 3.4.14** (Embargoes). For the embargo multiplier $\sqcup \ltimes \mathbf{!} := (\mathrm{Id}, \top) : \mathcal{W} \to \mathcal{W} \times \uparrow$ (example 3.3.9) for $\mathbf{!} := (\top, \top)$, a morphism $((), ()) : (W, o) \to \mathbf{!}$ is dimensionally split if $o = \top$, with the identity as an invertible dimensional section. The multiplier $\sqcup \ltimes \mathbf{!}$ is $\top$-slice shard-free.

For $\sqcup \ltimes (\mathbf{!} \ltimes U) : (W, o) \mapsto (W \ltimes U, o)$, a morphism $(\varphi, ()) : (W, o) \to (U, \top) = (\mathbf{!} \ltimes U)$ is dimensionally split if $\varphi : W \to U$ is dimensionally split for $\sqcup \ltimes U$. If $\chi : W' \ltimes U \to W$ is a dimensional section for $\varphi$, then $(\chi, \mathrm{id}_o) : (W' \ltimes U, o) \to (W, o)$ is a dimensional section for $(\varphi, ())$. $\top$-slice shard-freedom is then inherited from $\sqcup \ltimes U$.

**Example 3.4.15** (Enhanced embargoes). For the enhanced embargo multiplier $\sqcup \ltimes \mathbf{!} : \mathcal{W} \to \mathcal{W}_\mathbf{I} = \mathcal{W}_\perp / \mathcal{W} : W \mapsto (W \xrightarrow{\mathrm{id}} W)$ (example 3.3.10), a morphism $(V \xrightarrow{\varphi} W) \to (\top \to \top) = \mathbf{!}$ is dimensionally split if $V \neq \perp$, with dimensional section $(\mathrm{id}_V, \varphi) : (V \to V) \to (V \xrightarrow{\varphi} W)$. This multiplier is generally not $\top$-slice shard-free: since it only produces identity arrows, any dimensionally split non-identity arrow is a shard.

For $\sqcup \ltimes (U \ltimes \mathbf{!}) : (V \to W) \mapsto (V \ltimes U \to W \ltimes U)$, a morphism $(V \to W) \to (U \to U) = (U \ltimes \mathbf{!})$ is dimensionally split (with section $([], \chi) : (\perp \to W' \ltimes U) \to (V \to W)$) if the morphism $W \to U$ is dimensionally split for $\sqcup \ltimes U$ with section $\chi : W' \ltimes U \to W$. The multiplier $\sqcup \ltimes (U \ltimes \mathbf{!})$ is generally not $\top$-slice shard-free, as the domain part of a dimensionally split morphism could be anything.

For $\sqcup \ltimes (\mathbf{!} \ltimes U) : (V \to W) \mapsto (V \ltimes U \to W)$, any morphism $(V \to W) \to (U \to \top) = (\mathbf{!} \ltimes U)$ is dimensionally split by

$$([], \mathrm{id}) : (\perp \to W) \ltimes (\mathbf{!} \ltimes U) = (\perp \to W) \to (V \to W). \quad (21)$$

This multiplier is therefore generally not $\top$-slice shard-free.

To conclude, we have made the base category more complicated in order to be able to define the latter multiplier, but as a trade-off we now have shards to deal with.

**Example 3.4.16** (Erasure). In the category $\mathrm{Erase}_d$ (example 3.3.12) with multiplier $\sqcup \times i$, all morphisms to $i$ are dimensionally split with the identity as an invertible dimensional section. The multiplier is shard-free.

### 3.4.4 Boundaries

**Definition 3.4.17.** The boundary $\partial U$ of a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is a presheaf over $\mathcal{V}$ such that the cells $V \Rightarrow \partial U$ are precisely the morphisms $V \to U$ that are *not* dimensionally split.

This is a valid presheaf by proposition 3.4.8.

**Proposition 3.4.18.** If $\sqcup \ltimes U$ is $\top$-slice objectwise pointable, then $\partial U$ is the largest strict subobject of $\mathbf{y}U$.

18