106 Case studies

path type is monotone in its sole type argument, and so does not pose a problem in this regard.

### 5.3 Identity types

Our final illustrative example of the schema we wish to implement is not a higher inductive type at all, merely an ordinary indexed inductive type: Martin Löf's identity type with its J elimination rule (Section 2.1.5.4). While non-indexed inductive types such as Nat can be adapted to the cubical setting without any change, indexed inductive types are a different story; we will see that the implementation of their Kan operations requires tactics similar to those we have used for higher inductive types.

The identity type at $A$ is a type indexed by two elements of $A$, which is inhabited by refl when those two elements are the same.

$$A : \cup \gg \text{inductive } \text{Id}(A, a : A, a' : A) \text{ where}$$
$$| \text{refl}(a : A) \in \text{Id}(A, a, a)$$

Deriving the elimination rule for this type following Dybjer [Dyb94], we arrive at the so-called J rule, the elimination rule previously described in Section 2.1.5.4.

$$\frac{M_0 \in A \quad M_1 \in A \quad P \in \text{Id}(A, M_0, M_1) \quad a : A \gg N \in B[a/a_0, a/a_1, \text{refl}(a)/p]}{\text{elim}(a_0, a_1, p, B; M_0, M_1; P; a, N) \in B[M_0/a_0, M_1/a_1, P/p]}$$

$$\frac{M \in A \quad a : A \gg N \in B[a/a_0, a/a_1, \text{refl}(a)/p]}{\text{elim}(a_0, a_1, p, B; M, M; \text{refl}(M); a, N) = N[M/a] \in B[M/a_0, M/a_1, \text{refl}(M)/p]}$$

In words, in order to construct a map into a type $B$ predicated on two elements of $A$ and an identity between them, it suffices to provide a clause for the refl case. Note that this elimination principle does not, for example, directly provide any way of constructing functions into type families such as $a : A, p : \text{Id}(A, a, a) \gg B'$ type.

Naively, we might try to interpret $\text{Id}(A, M_0, M_1)$ as the relation consisting only of a refl value whenever $M_0$ and $M_1$ are exactly equal in $A$. However, this definition fails to support coercion. We can see this by observing that coercion requires $\text{Id}(A, M_0, M_1)$ to be inhabited not only when $M_0$ and $M_1$ are exactly equal, but whenever there is a path $P \in \text{Path}(A, M_0, M_1)$ between them.

$$\text{coe}_{x:\text{Id}(A, M_0, P, x)}^{0 \to 1}(\text{refl}(M_0)) \in \text{Id}(A, M_0, M_1)$$