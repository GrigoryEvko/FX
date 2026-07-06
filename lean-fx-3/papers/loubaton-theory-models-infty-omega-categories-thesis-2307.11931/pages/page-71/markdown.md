1.2. GRAY OPERATIONS

cone, the Gray o-cone or an iterated suspension, and suppose given a square

$$\begin{array}{c} G(\mathbf{D}_{n-1}) \xrightarrow{\nabla_{n-1,k}} G(\mathbf{D}_{n-1} \coprod_k \mathbf{D}_{n-1}) \\ \searrow G(i_n^-) \searrow \searrow G(\mathbf{D}_n) \xrightarrow{f} G(\mathbf{D}_n \coprod_k \mathbf{D}_n) \\ \searrow G(i_n^+) \searrow \searrow G(i_n^+) \coprod_k G(i_n^+) \\ G(\mathbf{D}_{n-1}) \xrightarrow{\nabla_{n-1,k}} G(\mathbf{D}_{n-1} \coprod_k \mathbf{D}_{n-1}) \end{array}$$

where we set $\nabla_{n,n} := id$. Then, the morphism $f$ is $G(\nabla_{n,k})$.

Proof. As the proof for any possibilities of $G$ are similar, we will show only the case $G := \_ \otimes [1]$. As for any integer $n$, $\mathbf{D}_n \otimes [1]$ admits a loop free and atomic basis, we can then show the desired assertion after applying the functor $\lambda$. Suppose first that $k < n-1$. By assumption, we have

$$\partial f(e_n \otimes \{\alpha\}) = \partial(e_n^0 \otimes \{\alpha\} + e_n^1 \otimes \{\alpha\})$$

$$\partial f(e_n \otimes [1]) = \partial(e_n^0 \otimes [1]) + \partial(e_n^1 \otimes [1])$$

This forces the equalities

$$f(e_n \otimes \{\alpha\}) = e_n^0 \otimes \{\alpha\} + e_n^1 \otimes \{\alpha\}$$

$$f(e_n \otimes [1]) = e_n^0 \otimes [1] + e_n^1 \otimes [1]$$

and $f$ is then equal to $\nabla_{n,k} \otimes [1]$. The case $k = n-1$ is similar.

Proof of theorem 1.2.3.18. As every globular sum is a colimit of globes, we can extend $\psi$ to a (a priori non natural) transformation, $\psi : F_{|\Theta} \to G_{|\Theta}$. Let $\Theta'$ be the maximal sub category of $\Theta$ such that $\psi_{\Theta'}$ is an equality. As $G(\mathbf{D}_n)$ does not have non trivial automorphisms, the assumption implies that $\Theta'$ fulfills the first condition of lemma 1.2.3.20. The lemma 1.2.3.21 implies that it fulfills the second condition, and an easy induction on $(n-k)$ using lemma 1.2.3.22 implies that it fulfills the last condition. Applying the lemma 1.2.3.20, this concludes the proof.

61