27:34

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

Case: $\Gamma = \Delta.(\mu \mid A)$

In this case, we note that $[\![\Gamma]\!] = [\![\Delta]\!] \times_{\mathcal{G}(\mu)(\mathsf{T}\mathsf{y}_n^*)} \mathcal{G}(\mu)(\mathsf{T}\mathsf{m}_n^*)$ and, since pullback are computed pointwise, it suffices to construct element of $\pi_1([\![\Delta]\!]_\Gamma)$ and $\pi_1(\mathcal{G}(\mu)(\mathsf{T}\mathsf{m}_n^*)_\Gamma)$ separately which agree on $\pi_1(\mathcal{G}(\mu)(\mathsf{T}\mathsf{y}_n^*)_\Gamma)$.

First, we reindex $\mathsf{atoms}_\Delta$ by $\Gamma \vdash \uparrow : \Delta @ m$ to obtain $\delta \in \pi_1([\![\Delta]\!]_\Gamma)$. Next, using the element $\mathbf{v}_0 \in \mathcal{G}(\mu)(\mathsf{Ne}_n(A))_\Gamma$. It is easily seen that these agree on $\pi_1(\mathcal{G}(\mu)(\mathsf{T}\mathsf{y}_n^*)_\Gamma)$. The check that this lies over $\mathsf{id}$ follows from the fact that (1) $\delta$ lies over $\uparrow$, (2) $\uparrow_A \mathbf{v}_0$ lies over $\mathbf{v}_0$ and (3) that $\uparrow.\mathbf{v}_0 = \mathsf{id}$.

Case: $\Gamma = \Delta.\{\mu\}$

We define $\mathsf{atoms}_\Gamma = \mathcal{G}(\mu)!(\mathsf{atoms}_\Delta)$. The check that this lies over $\mathsf{id}$ amounts to the equation in syntax that $\mathsf{id}.\{\mu\} = \mathsf{id}$.

Remark 6.3. $\mathsf{atoms}_\Gamma$ is analogous to the initial environment used in classical NbE proofs to kick off normalization. Abel [Abe13], for instance, denotes the environment $\uparrow^\Gamma$.

Combining Lemma 6.2 with the argument above, we conclude that for term $\Gamma \vdash M : A @ m$, there exists $\Gamma \vdash^{\mathsf{nf}} u : A @ m$ such that $|u| = M$. Moreover, because we have consistently worked with equivalences class of terms, this function automatically respects definitional equality. Summarizing:

Theorem 6.4. There is a function $\mathbf{nf}_\Gamma(-, A)$ sending terms of type $\Gamma \vdash A @ m$ to normal forms such that

(1) If $\Gamma \vdash M : A @ m$ then $\Gamma \vdash |\mathbf{nf}_\Gamma(M, A)| = M : A @ m$.
(2) If $\Gamma \vdash M = N : A @ m$ then $\mathbf{nf}_\Gamma(M, A) = \mathbf{nf}_\Gamma(N, A)$.

We can repeat this process to normalize types instead of terms. Given $\Gamma \vdash A @ m$, we obtain $[\![A]\!] : [\![\Gamma]\!] \longrightarrow \mathsf{T}\mathsf{y}_m^*$ which unfolds to an analogous diagram with only a small change: rather than using $\uparrow$ to pass from $\pi_1(\mathsf{T}\mathsf{m}_m^*)$ to normal forms, we use code to shift from $\mathsf{T}\mathsf{y}_m^*$ to normal types:

$$\begin{array}{c} \pi_1([\![\Gamma]\!]) \longrightarrow \pi_1(\mathsf{T}\mathsf{y}_m^*) \longrightarrow \pi_1(\mathsf{Nf}\mathsf{T}\mathsf{y}_m) \\ \alpha \circ [\![\Gamma]\!] \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbf{i}[m]^*(\mathbf{y}(\Gamma)) \xrightarrow[\mathbf{i}[m]^*(\lfloor A \rfloor)]{} \mathbf{i}[m]^*(\mathcal{T}_m) \end{array}$$

By again pushing $\mathsf{atoms}_\Gamma$ along the top of this diagram, we obtain a normalization function for types.

Theorem 6.5. There is a function $\mathbf{nfty}_\Gamma(-)$ sending types to normal types such that

(1) If $\Gamma \vdash A @ m$ then $\Gamma \vdash |\mathbf{nfty}_\Gamma(A)| = A @ m$.
(2) If $\Gamma \vdash A = B @ m$ then $\mathbf{nfty}_\Gamma(A) = \mathbf{nfty}_\Gamma(B)$.

6.2. Corollaries of normalization. A number of important theorems follow as corollaries of Theorems 6.4 and 6.5. For instance, we can reduce the decidability of conversion to the decidability of normal forms.

Corollary 6.6.

(1) $\Gamma \vdash M = N : A @ m$ iff $\mathbf{nf}_\Gamma(M, A) = \mathbf{nf}_\Gamma(N, A)$.
(2) $\Gamma \vdash A = B @ m$ iff $\mathbf{nfty}_\Gamma(A) = \mathbf{nfty}_\Gamma(B)$.