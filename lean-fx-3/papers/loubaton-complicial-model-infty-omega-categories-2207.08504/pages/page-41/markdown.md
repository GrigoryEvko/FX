1.2. GRAY OPERATIONS

- $$(K \otimes L)^*$$ is given on all integer $$n$$ by :

$$(K \otimes L)_n^* := \oplus_{k+l=n} K_k^* \otimes L_l^*.$$

- $$e \otimes f : K_0 \otimes L_0 \to \mathbb{Z}$$ is the unique morphism fulfilling

$$(e \otimes f)(x \otimes y) = e(x)f(y).$$

The Gray tensor product induces a monoidal structure on ADC. Its unit is given by $$\lambda\mathbf{D}_0$$. Furthermore, Steiner shows that if $$K$$ and $$L$$ admit loop free and unitary bases, so does $$K \otimes L$$. The basis of $$K \otimes L$$ is given by the set of elements of shape $$b \otimes b'$$ where $$b$$ and $$b'$$ are respectively elements of the bases of $$K$$ and $$L$$. The monoidal structure then restricts to a monoidal structure on $$\mathrm{ADC_B}$$.

**Notation 1.2.3.2.** To simplify notation, the augmented directed complex $$\lambda[1]$$ will simply be denoted by [1].

**Definition 1.2.3.3.** The induced functor

$$\_ \otimes [1] : \mathrm{ADC} \to \mathrm{ADC}$$

is called the *Gray cylinder*. For $$(K, K^*, e)$$ an augmented directed complex, we then have

$$(K, K^*, e) \otimes [1] := (K \otimes [1], (K \otimes [1])^*, e)$$

where

- $$K \otimes [1]$$ is the chain complex whose value on $$n$$ is:

$$(K \otimes [1])_n := \begin{cases} \{x \otimes \{\epsilon\}, x \in K_0, \epsilon = 0, 1\} & \text{if } n = 0 \\ \{x \otimes \{\epsilon\}, x \in K_n, \epsilon = 0, 1\} \oplus \{x \otimes [1], x \in K_{n-1}\} & \text{if } n > 0 \end{cases}$$

and the differential is the unique graded group morphism fulfilling:

$$\partial(x \otimes [1]) := \partial x \otimes [1] + (-1)^{|x|} (x \otimes \{1\} - x \otimes \{0\}) \quad \partial(x \otimes \{\epsilon\}) = (\partial x) \otimes \{\epsilon\}$$

for $$\epsilon \in \{0, 1\}$$, and where we set the convention $$\partial x := 0$$ if $$|x| = 0$$.

- $$(K \otimes [1])^*$$ is given on all integer $$n$$ by :

$$(K \otimes [1])_n^* := \begin{cases} \{x \otimes \{\epsilon\}, x \in K_0^*, \epsilon = 0, 1\} & \text{if } n = 0 \\ \{x \otimes \{\epsilon\}, x \in K_n^*, \epsilon = 0, 1\} \oplus \{x \otimes [1], x \in K_{n-1}^*\} & \text{if } n > 0 \end{cases}$$

- $$e : (K \otimes [1])_0 \to \mathbb{Z}$$ is the unique morphism fulfilling

$$e(x \otimes \{0\}) = e(x \otimes \{1\}) = e(x).$$

**Proposition 1.2.3.4.** *Let $$A$$ be an augmented directed complex admitting no non-trivial automorphisms. Then the augmented directed complexe $$A \otimes [1]$$ has no non-trivial automorphisms.*

*Proof.* Let $$\phi : A \otimes [1] \to A \otimes [1]$$ be an automorphism. The morphism $$\phi$$ then induces a bijection on the elements of the basis of $$A \otimes [1]$$.

Let $$(E, F)$$ be a partition of the set $$(B_{A \otimes [1]})_0$$ such that

41