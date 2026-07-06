(c) We have

$$\exists_{U}^{W_0} \exists_{U}^{W_0}(W, \psi) = \exists_{U}^{W_0}(W \times U, \psi \times U) \cong (W \times U, \pi_1 \circ (\psi \times U)) = (W \times U, \psi \circ \pi_1). \ \square$$

**Theorem 3.5.11** (Slicewise quotient theorem$^{8/9}$). If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice (or equivalently slicewise, for either notion of shard-freedom) fully faithful and shard-free, then

1. (Obsolete.) $\exists_{U}^{W_0} : \mathcal{W}/W_0 \simeq (\mathcal{V}//U)/(W_0 \ltimes U, \pi_2)$ is an equivalence of categories,$^{13}$

2. $\exists_{U}^{W_0} : \mathcal{W}/W_0 \simeq \mathcal{V}//(W_0 \ltimes U)$ is an equivalence of categories.

### 3.6 Composing multipliers

**Theorem 3.6.1.** If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is a multiplier for $U$ and $\sqcup \ltimes U' : \mathcal{V} \to \mathcal{V}'$ is a multiplier for $U'$, then their composite $\sqcup \ltimes (U \ltimes U') := (\sqcup \ltimes U) \ltimes U'$ is a multiplier for $U \ltimes U'$.

1. The functor $\exists_{U \ltimes U'} : \mathcal{W} \to \mathcal{V}'/(U \ltimes U')$ equals $\exists_{U'}^{U'} \circ \exists_{U}$.

2. The functor $\exists_{U \ltimes U'}^{W_0} : \mathcal{W} \to \mathcal{V}'/(U \ltimes U')$ equals $\exists_{U'}^{W_0 \ltimes U} \circ \exists_{U}^{W_0}$.

3. Assume both multipliers are endo. Then:

(a) The composite $\sqcup \ltimes (U \ltimes U')$ is copointed if $\sqcup \ltimes U$ and $\sqcup \ltimes U'$ are copointed,

(b) The composite $\sqcup \ltimes (U \ltimes U')$ is a comonad if $\sqcup \ltimes U$ and $\sqcup \ltimes U'$ are comonads,

(c) The composite $\sqcup \ltimes (U \ltimes U')$ is cartesian if $\sqcup \ltimes U$ and $\sqcup \ltimes U'$ are cartesian.

4. The composite $\sqcup \ltimes (U \ltimes U')$ is $\top$-slice faithful if $\sqcup \ltimes U$ and $\sqcup \ltimes U'$ are $\top$-slice faithful.

5. The composite $\sqcup \ltimes (U \ltimes U')$ is $\top$-slice full if $\sqcup \ltimes U$ is $\top$-slice full and $\sqcup \ltimes U'$ is slicewise full.

6. The composite $\sqcup \ltimes (U \ltimes U')$ is slicewise full if $\sqcup \ltimes U$ and $\sqcup \ltimes U'$ are slicewise full.

7. The composite $\sqcup \ltimes (U \ltimes U')$ is $\top$-slice shard-free if $\sqcup \ltimes U$ is $\top$-slice shard-free and $\sqcup \ltimes U'$ is slicewise full and shard-free.

8. (a) (Obsolete). The composite $\sqcup \ltimes (U \ltimes U')$ is indirectly slicewise shard-free if $\sqcup \ltimes U$ is indirectly slicewise shard-free and $\sqcup \ltimes U'$ is slicewise full and indirectly slicewise shard-free.

(b) The composite $\sqcup \ltimes (U \ltimes U')$ is directly slicewise shard-free if $\sqcup \ltimes U$ is directly slicewise shard-free and $\sqcup \ltimes U'$ is slicewise full and directly slicewise shard-free.

9. The composite $\sqcup \ltimes (U \ltimes U')$ is $\top$-slice right adjoint if $\sqcup \ltimes U$ and $\sqcup \ltimes U'$ are $\top$-slice right adjoint, and in that case we have:

(a) $\exists_{U \ltimes U'} = \exists_{U} \circ \exists_{U'}^{U}$,

(b) $\exists_{U \ltimes U'}^{W_0} = \exists_{U}^{W_0} \circ \exists_{U'}^{W_0 \ltimes U}$.

*Proof.* Since $\top \ltimes U \cong U$, we see that $(\top \ltimes U) \ltimes U' \cong U \ltimes U'$, so the composite is indeed a multiplier for $U \ltimes U'$.

1-2. Follows from expanding the definitions.

3. (a) Copointed endofunctors compose.

(b) Comonads compose. They most certainly do not!

(c) By associativity of the cartesian product.

$^{13}$We use a slight abuse of notation by using $(\mathcal{V}//U)/(W_0 \ltimes U, \pi_2)$ as a subcategory of $\mathcal{V}/(W_0 \ltimes U)$.

23