CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

Definition 1.2.3.9. We define the suspension as the functor

$$[\_, 1] : \mathrm{ADC} \to \mathrm{ADC}$$

where $[K, 1]$ is defined as the following pushout:

$$\begin{array}{c} K \otimes \{0, 1\} \longrightarrow K \otimes [1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ 1 \coprod 1 \longrightarrow [K, 1] \end{array} \tag{1.2.3.10}$$

We leave to the reader to check that $[K, 1]$ admits a loop free and unitary basis when this is the case for $K$. This functor then induces a functor:

$$[\_, 1] : \mathrm{ADC_B} \to \mathrm{ADC_B}$$

Remark 1.2.3.11. Unfolding the definition, we have

$$[(K, K', e), 1] := ([K, 1], ([K, 1])^*, e)$$

where

- $[K, 1]$ is the chain complex whose value on $n$ is:

$$[K, 1] := \left\{ \begin{array}{ll} \mathbb{Z}[\{0\}, \{1\}] & \text{if } n = 0 \\ \{[x, 1], x \in K_{n-1}\} & \text{if } n > 0 \end{array} \right.$$

and the differential is the unique graded group morphism fulfilling:

$$\partial([x, 1]) := \left\{ \begin{array}{ll} \{1\} - \{0\} & \text{if } |x| = 0 \\ [\partial x, 1] & \text{if } |x| > 0 \end{array} \right.$$

- $([K, 1])^*$ is given on all integer $n$ by:

$$([K, 1])_n^* := \left\{ \begin{array}{ll} \mathbb{N}[0, 1] & \text{if } n = 0 \\ \{[x, 1], x \in K_{n-1}^*\} & \text{if } n > 0 \end{array} \right.$$

- $e : ([K, 1])_0 \to \mathbb{Z}$ is the unique morphism fulfilling

$$e(0) = e(1) = e(x).$$

The basis of $[K, 1]$ is given by the reunion of $\{0\}$, $\{1\}$ and of the set of elements of shape $[b, 1]$ where $b$ is an element of the basis of $K$.

Proposition 1.2.3.12. Let $A$ be a non null augmented directed complex admitting no non-trivial automorphisms. Then the augmented directed complex $[A, 1]$ has no non-trivial automorphisms.

Proof. Let $\phi : [A, 1] \to [A, 1]$ be an automorphism. As the element $\{1\} \in ([A, 1])_0$ is the only element of the basis such that for all $v \in [A, 1]_1$ $\partial_0^-(v) \neq \{1\}$, it is preserved by $\phi$. As a consequence, $\phi$ also preserves $\{0\}$. The induced morphism $\phi_0 : [A, 1]_0 \to [A, 1]_0$ is then the identity.

Now, remark that $(\phi_{n+1})_{n \in \mathbb{N}} : A \to A$ is an automorphism and is then the identity. This implies that for all $n > 0$, $\phi_n : [A, 1]_n \to [A, 1]_n$ is then identity, which concludes the proof.

44