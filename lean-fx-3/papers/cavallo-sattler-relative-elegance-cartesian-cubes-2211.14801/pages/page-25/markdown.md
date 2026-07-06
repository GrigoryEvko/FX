Relative Elegance and Cartesian Cubes with One Connection

25

spans in finite sets whose second leg is surjective. This can be strictified to a 1-category by replacing relations with Boolean-valued matrices.

Recall that the category of algebras $\operatorname{Alg}(\mathbf{T}) := [\mathbf{T}, \mathbf{Set}]_{\mathrm{fp}}$ of a Lawvere theory $\mathbf{T}$ is the category of finite-product-preserving functors from $\mathbf{T}$ to $\mathbf{Set}$, which supports an "underlying set" functor $U: [\mathbf{T}, \mathbf{Set}]_{\mathrm{fp}} \to \mathbf{Set}$ given by evaluation at the distinguished object $T^1$. This functor has a left adjoint $F: \mathbf{Set} \to \operatorname{Alg}(\mathbf{T})$ which produces the free $\mathbf{T}$-algebra on a set, and the covariant Yoneda embedding restricts to an embedding $\mathbf{T}^{\mathrm{op}} \to \operatorname{Alg}(\mathbf{T})$ sending $T^n$ to the free algebra on $n$ elements. We write $\mathbf{SLat}$ and $\mathbf{01SLat}$ for the categories of algebras of $\mathbf{T}_{\vee}$ and $\square_{\vee}$ respectively. Concretely, these are the categories of sets equipped with the operations described in Definition 4.1 and operation-preserving morphisms between them.

It can also be useful to take an order-theoretic perspective on $\mathbf{SLat}$ and $\mathbf{01SLat}$, identifying them as subcategories of the category $\mathbf{Pos}$ of posets and monotone maps. Recall that the operator $\vee$ induces a poset structure on any semilattice, with $x \leq y$ when $x \vee y = y$.

Proposition 4.3 $\mathbf{SLat}$ is equivalent to the subcategory of $\mathbf{Pos}$ consisting of posets with finite non-empty joins (that is, least upper bounds) and monotone maps that preserve said joins. $\mathbf{01SLat}$ is equivalent to the further (non-full) subcategory of posets that also have a minimum and maximum element and monotone maps that also preserve them.

Remark 4.4 Any finite linear order is a semilattice, and it is 01-bounded if it is inhabited. Moreover, any monotone map between linear orders preserves joins. Thus the inclusion $\Delta \to \mathbf{Pos}$ factors through a fully faithful inclusion $\Delta \to \mathbf{SLat}$.

In particular, the interval $[1] \in \mathbf{Pos}$ is a 01-bounded semilattice.

Proposition 4.5 The interval is a dualizing object for a duality between the categories of finite semilattices and finite 01-bounded semilattices, which is to say that we have the following categorical equivalence:

$$\mathbf{SLat}_{\mathrm{fin}}^{\mathrm{op}} \xleftarrow[\mathrm{01SLat}(-, [1])]{\mathrm{SLat}(-, [1])} \mathbf{01SLat}_{\mathrm{fin}}.$$

Proof By a slight variation on the argument that $\mathbf{0SLat}_{\mathrm{fin}}^{\mathrm{op}} \simeq \mathbf{0SLat}_{\mathrm{fin}}$ indicated in [Joh82, §VI3.6, §VI.4.6(b)].

Given a semilattice $A$, the 01-bounded semilattice structure on $\mathbf{SLat}(A, [1])$ is defined pointwise from that on $[1]$; likewise $\mathbf{01SLat}(B, [1])$ has a pointwise semilattice structure for any $B \in \mathbf{01SLat}$. This extends the duality between the augmented simplex category and the category of finite intervals (i.e., finite bounded linear orders and bound-preserving monotone maps) observed by Joyal [Joy97, §1.1; Wra93].

2025/10/16 00:43