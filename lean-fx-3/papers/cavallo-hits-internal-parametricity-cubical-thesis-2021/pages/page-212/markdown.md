200

Programming with parametricity

Next, we know that swapping iterated bridge and path types is an isomorphism, so it is enough to prove the following isomorphism where we have flipped the order of type constructors on either side.

$$\operatorname{Path}(\operatorname{Bridge}(x.G_x, a, b), q_0, q_1) \simeq \operatorname{Bridge}(\operatorname{Bridge}(x.G_x, a, b), q_0, q_1)$$

Finally, we know that $\operatorname{Bridge}(x.G_x, a, b) \simeq R$. Thus this follows directly from bridge-discreteness of $R$.

**Corollary 10.3.11.** $U_{\text{bdisc}}$ is relativistic. That is, for any $A, B: U_{\text{bdisc}}$, we have the following isomorphism with the forward map given by the bridge type former (which preserves bridge-discreteness per Theorem 10.3.6).

$$\operatorname{Bridge}(U_{\text{bdisc}}, A, B) \simeq (\operatorname{fst}(A) \times \operatorname{fst}(B) \to U_{\text{bdisc}})$$

*Proof.* Suppose $A = \langle A_0, p \rangle$ and $B = \langle B_0, q \rangle$. By Lemma 9.2.3, $\operatorname{Bridge}(U_{\text{bdisc}}, A, B)$ is isomorphic to the following.

$$(C: \operatorname{Bridge}(U, A_0, B_0)) \times \operatorname{Bridge}(x.\operatorname{IsBDisc}(C x), p, q)$$

The right hand type, meanwhile, is also isomorphic to a product.

$$(R: A_0 \times B_0 \to U) \times ((a: A) (b: B) \to \operatorname{IsBDisc}(R \langle a, b \rangle))$$

We have an isomorphism between the first components by relativity of $U$, implemented by the bridge and Gel types. Each second component, meanwhile, is a proposition. (For the first, it is straightforward to check that the bridge type of a proposition is a proposition.) It therefore suffices to show that the isomorphism of the first components takes $C$ such that $\operatorname{Bridge}(x.\operatorname{IsBDisc}(C x), p, q)$ to $R$ such that $((a: A) (b: B) \to \operatorname{IsBDisc}(R \langle a, b \rangle))$ and vice versa. The forward direction is the fact that bridge-types preserve bridge-discreteness, the converse is the fact that Gel-types preserve the same.

Note that the relativity of $U_{\text{bdisc}}$ implies that $U_{\text{bdisc}}$ itself is not bridge discrete.

*Example 10.3.12.* $\mathbb{B}_{\text{bdisc}} := (A: U_{\text{bdisc}}) \to \operatorname{fst}(A) \to \operatorname{fst}(A) \to \operatorname{fst}(A)$ is isomorphic to $\operatorname{Bool}$.

*Proof (Sketch).* Suppose we are given $c: \mathbb{B}_{\text{bdisc}}$. Given $A: U_{\text{bdisc}}$, $t: \operatorname{fst}(A)$ and $f: \operatorname{fst}(A)$, we define a relation $R \in \operatorname{Bool} \times \operatorname{fst}(A) \to U$ as in Theorem 10.1.2.

$$R := \lambda \langle b, a \rangle. \operatorname{Path}(\operatorname{fst}(A), \operatorname{elim}_{\operatorname{Bool}}(\dots \operatorname{fst}(A); b; t, f), a) \in \operatorname{Bool} \times \operatorname{fst}(A) \to U$$

The type $\operatorname{fst}(A)$ is bridge-discrete by assumption and bridge-discrete types are closed under path types, so this relation is pointwise bridge-discrete. Thus Theorem 10.3.10 gives us a bridge in $U_{\text{bdisc}}$ from $\operatorname{Bool}$ (coupled with the proof of bridge-discreteness from Theorem 10.3.7) to $A$ corresponding to $R$. Applying $c$ at this bridge, we then proceed as in the proof of Theorem 10.3.10.