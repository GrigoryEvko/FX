1.2. GRAY OPERATIONS

### 1.2.2.7. Unfolding the definition, we have

$$
(K, K', e) \star 1 := (K \star 1, (K \star 1)^*, e) \quad 1 \stackrel{co}{\star} (K, K', e) := (1 \stackrel{co}{\star} K, (1 \stackrel{co}{\star} K)^*, e)
$$

where

- $K \star 1$ and $1 \stackrel{co}{\star} K$ are the chain complex whose value on $n$ are:

$$
(K \star 1)_n := \left\{ \begin{array}{ll} \mathbb{Z}[\emptyset \star 1] \oplus \{x \star \emptyset, x \in K_0\} & \text{if } n = 0 \\ \{\emptyset \star x, x \in K_n\} \oplus \{x \star 1, x \in K_{n-1}\} & \text{if } n > 0 \end{array} \right.
$$

$$
(1 \stackrel{co}{\star} K)^n := \left\{ \begin{array}{ll} \mathbb{Z}[1 \stackrel{co}{\star} \emptyset] \oplus \{\emptyset \stackrel{co}{\star} x, x \in K_0\} & \text{if } n = 0 \\ \{\emptyset \stackrel{co}{\star} x, x \in K_n\} \oplus \{1 \stackrel{co}{\star} x, x \in K_{n-1}\} & \text{if } n > 0 \end{array} \right.
$$

and the differentials are the unique graded group morphisms fulfilling:

$$
\partial(x \star 1) = \partial x \star 1 + (-1)^{|x|} x \star \emptyset \quad \partial(x \star \emptyset) = \partial x \star \emptyset
$$

$$
\partial(1 \stackrel{co}{\star} x) = 1 \stackrel{co}{\star} \partial x + (-1)^{|x|} \emptyset \stackrel{co}{\star} x \quad \partial(\emptyset \stackrel{co}{\star} x) = \emptyset \stackrel{co}{\star} x
$$

where we set the convention $\partial x := 0$ if $|x| = 0$.

- The graded monoids $(K \star 1)^*$ and $(1 \stackrel{co}{\star} K)^*$ are given on all integer $n$ by:

$$
(K \star 1)^* := \left\{ \begin{array}{ll} \mathbb{N}[\emptyset \star 1] \oplus \{x \star \emptyset, x \in K_0^*\} & \text{if } n = 0 \\ \{\emptyset \star x, x \in K_n^*\} \oplus \{x \star 1, x \in K_{n-1}^*\} & \text{if } n > 0 \end{array} \right.
$$

$$
(1 \stackrel{co}{\star} K)^* := \left\{ \begin{array}{ll} \mathbb{N}[1 \stackrel{co}{\star} \emptyset] \oplus \{\emptyset \stackrel{co}{\star} x, x \in K_0^*\} & \text{if } n = 0 \\ \{\emptyset \stackrel{co}{\star} x, x \in K_n^*\} \oplus \{1 \stackrel{co}{\star} x, x \in K_{n-1}^*\} & \text{if } n > 0 \end{array} \right.
$$

- The augmentations $e : (K \star 1)_0 \to \mathbb{Z}$ and $e : (1 \stackrel{co}{\star} K)_0 \to \mathbb{Z}$ are the unique ones fulfilling

$$
e(\emptyset \star 1) = 1 \quad e(x \star \emptyset) = e(x)
$$

$$
e(1 \stackrel{co}{\star} \emptyset) = 1 \quad e(\emptyset \stackrel{co}{\star} x) = e(x).
$$

**Proposition 1.2.2.8.** *Let $A$ be an augmented directed complex admitting no non-trivial automorphisms. Then the augmented directed complexes $A \star 1$ and $1 \stackrel{co}{\star} A$ have no non-trivial automorphisms.*

*Proof.* Let $\phi : A \star 1 \to A \star 1$ be an automorphism. The morphism $\phi$ then induces a bijection on the elements of the basis of $A \star 1$.

As the element $\emptyset \star 1 \in (A \star 1)_0$ is the only element of the basis such that for all $v \in (A \star 1)_1$ $\partial_0^-(v) \neq \emptyset \star 1$, it is preserved by $\phi$. As a consequence, for any element $x$ of the basis of $A_0$, $\phi(x \star \emptyset)$ is of shape $x' \star \emptyset$. The morphism $\phi$ then preserves $(A \star \emptyset)_0$.

49