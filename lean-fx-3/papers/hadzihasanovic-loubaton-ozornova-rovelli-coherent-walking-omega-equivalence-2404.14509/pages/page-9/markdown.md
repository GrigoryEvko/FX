A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

9

Remark 1.25. The $\omega$-functors $\alpha_k, \beta_k \colon \Sigma(\widehat{\omega\mathcal{E}}^{(k-1)}) \to \widehat{\omega\mathcal{E}}^{(k)}$ induce $\omega$-functors

$$\alpha_\infty, \beta_\infty \colon \Sigma(\widehat{\omega\mathcal{E}}) \to \widehat{\omega\mathcal{E}}.$$

The following result justifies the name of walking $\omega$-equivalence.

Proposition 1.26. Let $\mathcal{D}$ be an $\omega$-category. Given $a \in \mathcal{D}_n$, we have that $a \in \mathrm{bieq}_n\mathcal{D}$ if and only if there exists an $\omega$-functor $\tilde{a} \colon \Sigma^{n-1}(\widehat{\omega\mathcal{E}}) \to \mathcal{D}$ such that the following diagram commutes:

$$\begin{array}{c} \mathcal{C}_n \xrightarrow{\quad a \quad} \mathcal{D} \\ \Sigma^{n-1}f \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \Sigma^{n-1}(\widehat{\omega\mathcal{E}}) \end{array} \tag{1.27}$$

Proof. For each $n \ge 0$ and $a \in \mathrm{bieq}_n\mathcal{D}$, make a choice of $a^L, a^R \in \mathcal{D}_n$ and of $c_a, c'_a \in \mathrm{bieq}_{n+1}\mathcal{D}$ of the form

$$c_a \colon a^L \underset{n-1}{*} a \to \mathrm{id}_{d_{n-1}^-a} \quad \text{and} \quad c'_a \colon a \underset{n-1}{*} a^R \to \mathrm{id}_{d_{n-1}^+a}.$$

By recursion on $k \ge 0$, we construct families of $\omega$-functors

$$\tilde{a}^{(k)} \colon \Sigma^{n-1}\widehat{\omega\mathcal{E}}^{(k)} \to \mathcal{D}$$

parameterized by $n \ge 0$ and $a \in \mathrm{bieq}_n\mathcal{D}$, such that

$$\begin{array}{c} \mathcal{C}_n \xrightarrow{\quad a \quad} \mathcal{D} \\ \Sigma^{n-1}f \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \Sigma^{n-1}(\widehat{\omega\mathcal{E}}^{(k)}) \end{array}$$

commutes, and satisfying

$$(1.28) \ \tilde{a}^{(k-1)} = \tilde{a}^{(k)} \circ \Sigma^{n-1}(\iota_k) \text{ and } [\tilde{c}_a^{(k-1)}, \tilde{c}'_a^{(k-1)}] = \tilde{a}^{(k)} \circ [\Sigma^{n-1}(\alpha_k), \Sigma^{n-1}(\beta_k)]$$

for all $k > 0$. For each $n \in \mathbb{N}$ and $a \in \mathrm{bieq}_n\mathcal{D}$, we let $\tilde{a}^{(1)}$ be defined by

$$\Sigma^{n-1}f \mapsto a, \quad \Sigma^{n-1}g \mapsto a^L, \quad \Sigma^{n-1}g' \mapsto a^R,$$

and set $\tilde{a}^{(0)} := \tilde{a}^{(1)} \circ \Sigma^{n-1}(\iota_1)$. Then the equality

$$[\tilde{c}_a^{(0)}, \tilde{c}'_a^{(0)}] = \tilde{a}^{(1)} \circ [\Sigma^{n-1}(\alpha_1), \Sigma^{n-1}(\beta_1)]$$

holds by construction.

Let $k > 1$, $n \in \mathbb{N}$, and $a \in \mathrm{bieq}_n\mathcal{D}$. By the inductive hypothesis, we have a commutative diagram in $\omega\mathcal{C}at$

$$\begin{array}{c} \Sigma^n(\widehat{\omega\mathcal{E}}^{(k-2)}) \amalg \Sigma^n(\widehat{\omega\mathcal{E}}^{(k-2)}) \xrightarrow{[\Sigma^{n-1}(\alpha_{k-1}), \Sigma^{n-1}(\beta_{k-1})]} \Sigma^{n-1}(\widehat{\omega\mathcal{E}}^{(k-1)}) \\ \downarrow \Sigma^n(\iota_{k-1}) \amalg \Sigma^n(\iota_{k-1}) \\ \Sigma^n(\widehat{\omega\mathcal{E}}^{(k-1)}) \amalg \Sigma^n(\widehat{\omega\mathcal{E}}^{(k-1)}) \xrightarrow{[\tilde{c}_a^{(k-1)}, \tilde{c}'_a^{(k-1)}]} \mathcal{D}. \end{array}$$

Using the universal property of the pushout (1.23) and the fact that $\Sigma^{n-1}$ preserves pushouts by Proposition 1.1, we see that this diagram induces a unique $\omega$-functor

$$\tilde{a}^{(k)} \colon \Sigma^{n-1}\widehat{\omega\mathcal{E}}^{(k)} \to \mathcal{D}$$