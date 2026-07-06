1.2. GRAY OPERATIONS

Remark 1.2.3.7. Unfolding the definition, we have

$$(K, K', e) \star 1 := (K \star 1, (K \star 1)^*, e)$$

where

- $K \star 1$ is the chain complex whose value on $n$ is:

$$(K \star 1)_n := \begin{cases} \mathbb{Z}[\emptyset \star 1] \oplus \{x \star \emptyset, x \in K_0\} & \text{if } n = 0 \\ \{\emptyset \star x, x \in K_n\} \oplus \{x \star 1, x \in K_{n-1}\} & \text{if } n > 0 \end{cases}$$

and the differentials are the unique graded group morphisms fulfilling:

$$\partial(x \star 1) = \partial x \star 1 + (-1)^{|x|} x \star \emptyset \quad \partial(x \star \emptyset) = \partial x \star \emptyset$$

where we set the convention $\partial x := 0$ if $|x| = 0$.

- The graded monoids $(K \star 1)^*$ is given on any integer $n$ by :

$$(K \star 1)^* := \begin{cases} \mathbb{N}[\emptyset \star 1] \oplus \{x \star \emptyset, x \in K_0^*\} & \text{if } n = 0 \\ \{\emptyset \star x, x \in K_n^*\} \oplus \{x \star 1, x \in K_{n-1}^*\} & \text{if } n > 0 \end{cases}$$

- The augmentation $e : (K \star 1)_0 \to \mathbb{Z}$ is the unique ones fulfilling

$$e(\emptyset \star 1) = 1 \quad e(x \star \emptyset) = e(x)$$

The basis of $K \star 1$ is given by the reunion of $\emptyset \star 1$ and of the set of elements of shape $b \star 1$ where $b$ is an element of the basis of $K$.

Proposition 1.2.3.8. Let $A$ be an augmented directed complex admitting no non-trivial automorphisms. Then the augmented directed complexe $A \star 1$ has no non-trivial automorphisms.

Proof. Let $\phi : A \star 1 \to A \star 1$ be an automorphism. The morphism $\phi$ then induces a bijection on the elements of the basis of $A \star 1$.

As the element $\emptyset \star 1 \in (A \star 1)_0$ is the only element of the basis such that for all $v \in (A \star 1)_1$ $\partial_0^-(v) \neq \emptyset \star 1$, it is preserved by $\phi$. As a consequence, for any element $x$ of the basis of $A_0$, $\phi(x \star \emptyset)$ is of shape $x' \star \emptyset$. The morphism $\phi$ then preserves $(A \star \emptyset)_0$.

Now, remark that for any element $e \in (A \star 1)_{n+1}^*$, there exists $x \in A_n^*$ such that $x \star 1 \leq e$ if and only if there exists $y \in A_{n-1}^*$ such that $y \star 1 \leq \partial^+ e$. By a direct induction, this implies that there exists $x \in (A \star 1)_n^*$ such that $x \star 1 \leq e$ if and only if $\partial_0^+ e \in \mathbb{Z}[\emptyset \star 1]$.

Combined with the previous observation, this implies that for any element $x$ of the basis of $A_n$, $\phi(x \star \emptyset)$ is of shape $x' \star \emptyset$. The automorphism $\phi$ then induces by restriction an automorphism $\phi_{|A \star \emptyset} : A \to A$, and the hypothesis implies that it is the identity.

We now show by induction on $n$ that $\phi_n : (A \star 1)_n \to (A \star 1)_n$ is the identity. Suppose the result true at the stage $n$. For any element $x$ of the basis of $A_n$, we then have

$$\partial \phi(x \star 1) = \phi(\partial(x \star 1)) = \partial(x \star 1).$$

By the definition of the derivative of $A \star 1$, and as $\phi$ preserves the basis, this forces the equality $\phi(x \star 1) = x \star 1$. As we already know that for any element $x$ of the basis of $A_{n+1}$ we have $\phi(x \star \emptyset) = x \star \emptyset$, this concludes the induction.

We then have $\phi = id$ and $A \star 1$ has no non trivial automorphisms.

43