CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

As $i$ and $j$ are left Quillen functors, the induction hypothesis implies that $\psi(\partial\mathbf{D}_n): i(\partial\mathbf{D}_n) \to j(\partial\mathbf{D}_n)$ is a weak equivalence. $\square$

**Lemma 2.4.3.3.** *Morphisms $\psi((\mathbf{D}_n)_t): i((\mathbf{D}_n)_t) \to j((\mathbf{D}_n)_t)$ are weak equivalences.*

*Proof.* There is a diagram:

$$
\begin{array}{c}
i_{!}\mathbf{D}_{n-1} \xrightarrow[\sim]{\psi(\mathbf{D}_n)} j_{!}\mathbf{D}_{n-1} \\
i_{!}(i_{n}^{-}) \Big\downarrow \sim \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\
i_{!}(\mathbf{D}_n)_t \xrightarrow[\psi((\mathbf{D}_n)_t)]{} j_{!}(\mathbf{D}_n)_t
\end{array}
$$

By two out of three, this shows that $\psi((\mathbf{D}_n)_t)$ is a weak equivalence. $\square$

**Lemma 2.4.3.4.** *For any complicial set $Y$, the canonical morphism $N_j Y \to N_i Y$ is a weak equivalence.*

*Proof.* Let $Y$ be a complicial set. For any integer $n$, we have by adjunction a bijection

$$
\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\mathbf{D}_n, N_j Y) \cong \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\mathbf{D}_n, N_i Y)
$$

and according to lemmas 2.4.3.2 and 2.4.3.3, we have bijections

$$
\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\partial\mathbf{D}_n, N_j Y) \cong \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\partial\mathbf{D}_n, N_i Y)
$$

$$
\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}((\mathbf{D}_n)_t, N_j Y) \cong \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}((\mathbf{D}_n)_t, N_i Y).
$$

Let $a$ be an element of $\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\partial\mathbf{D}_n, N_j Y)$. We recall that the category $\pi_n(a, N_j Y)$ is defined in 2.4.1.11. The previous equivalences implies that we have an isomorphism of category

$$
\pi_n(a, N_j Y) \cong \pi_n(a, N_j Y).
$$

which concludes the proof according to theorem 2.4.2.9. $\square$

*Proof of the proposition 2.4.3.1.* Let $X$ be any marked simplicial set and $Y$ a complicial set. We have equalities:

$$
\begin{array}{ccc}
\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(j_{!}X, Y) & = & \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(X, j^*Y) \\
\downarrow & & \downarrow \\
\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(i_{!}X, Y) & = & \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(X, i^*Y)
\end{array}
$$

Lemma 2.4.3.4 implies that the right hand morphism is a bijection, and so is the left hand morphism. For any $X$, $\psi(X)$ is then a weak equivalence. $\square$

102