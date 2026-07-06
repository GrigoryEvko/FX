1.2. GRAY OPERATIONS

Lemma 1.2.4.18. Let $k < n$ be two integers, and $G$ be either the Gray cylinder, the Gray cone, the Gray o-cone or an iterated suspension, and suppose given a square

$$\begin{array}{c} G(\mathbf{D}_{n-1}) \xrightarrow{\nabla_{n-1,k}} G(\mathbf{D}_{n-1} \coprod_k \mathbf{D}_{n-1}) \\ \searrow G(i_n^-) \xrightarrow{} G(\mathbf{D}_n) \xrightarrow{f} G(\mathbf{D}_n \coprod_k G(i_n^-) \xrightarrow{} G(\mathbf{D}_n \coprod_k \mathbf{D}_n) \\ \searrow G(i_n^+) \xrightarrow{} G(i_n^+) \coprod_k G(i_n^+) \\ G(\mathbf{D}_{n-1}) \xrightarrow{\nabla_{n-1,k}} G(\mathbf{D}_{n-1} \coprod_k \mathbf{D}_{n-1}) \end{array}$$

where we set $\nabla_{n,n} := id$. Then, the morphism $f$ is $G(\nabla_{n,k})$.

Proof. As the proof for any possibilities of $G$ are similar, we will show only the case $G := \_ \otimes [1]$. As for any integer $n$, $\mathbf{D}_n \otimes [1]$ admits a loop free and atomic basis, we can then show the desired assertion after applying the functor $\lambda$. Suppose first that $k < n - 1$. By assumption, we have

$$\begin{array}{rcl} \partial f(e_n \otimes \{\alpha\}) & = & \partial(e_n^0 \otimes \{\alpha\}) + e_n^1 \otimes \{\alpha\}) \\ \partial f(e_n \otimes [1]) & = & \partial(e_n^0 \otimes [1]) + \partial(e_n^1 \otimes [1]) \end{array}$$

This forces the equalities

$$\begin{array}{rcl} f(e_n \otimes \{\alpha\}) & = & e_n^0 \otimes \{\alpha\} + e_n^1 \otimes \{\alpha\} \\ f(e_n \otimes [1]) & = & e_n^0 \otimes [1] + e_n^1 \otimes [1] \end{array}$$

and $f$ is then equal to $\nabla_{n,k} \otimes [1]$. The case $k = n - 1$ is similar.

Proof of theorem 1.2.4.15. As every globular sum is a colimit of globes, we can extend $\psi$ to a (a priori non natural) transformation, $\psi : F_{|\Theta} \to G_{|\Theta}$. Let $\Theta'$ be the maximal sub category of $\Theta$ such that $\psi_{|\Theta'}$ is natural. The category $\Theta'$ is closed by colimit. The assumption implies that $\Theta'$ fulfills the first condition of lemma 1.2.4.16. The lemma 1.2.4.17 implies that it fulfills the second condition, and an easy induction on $(n - k)$ using lemma 1.2.4.18 implies that it fulfills the last condition. Applying the lemma 1.2.4.16, $\psi : F_{|\Theta} \to G_{|\Theta}$ is then pointwise an isomorphism, and can be extended by colimits to a invertible natural transformation between $F$ and $G$. The unicity of this extension is a consequence of lemma 1.2.4.19.

We conclude this section by giving some technical results that we will use later.

Lemma 1.2.4.19. The set of $(0, \omega)$-categories admitting no non-trivial automorphisms is stable

(1) by isomorphisms,
(2) by $[\_, 1] \vee [1]$ and $[1] \vee [\_, 1]$,
(3) by the Gray cylinder, the Gray cone, the Gray o-cone, the Gray op-cone and the iterated suspensions,

and contains globular sums.

Proof. Let $S$ be the smallest set of $(0, \omega)$-categories stable by isomorphism, $[\_, 1] \vee [1]$, $[1] \vee [\_, 1]$, the Gray cylinder, the Gray cone and by iterated suspensions. As the set of $(0, \omega)$-categories admitting no non-trivial automorphisms is stable by dualities and by proposition 1.2.4.10, we have to show that it includes $S$.

51