forgetful functor $\infty\text{-Cat}^{+\infty} \rightarrow \infty\text{-Cat}$) induces an equivalence of categories between the categories of fibrant objects that preserves and detects weak equivalences and fibrations (between fibrant objects). Thus, their categories of fibrant objects are literally the same, with the same fibrations and weak equivalences.

Finally, in Section 4.4, we study a marked version of the Street nerve. The usual Street Nerve is the right adjoint functor $N_{\mathcal{O}}: \infty\text{-Cat} \rightarrow \mathbf{sSet}$, defined using Street's Orientals $\mathcal{O}: \Delta \rightarrow \infty\text{-Cat}$, where $N_{\mathcal{O}}(X)_n = \text{Hom}(\mathcal{O}[n], X)$. We extend it to a Nerve/realization Quillen adjunction:

$$|-|: \mathbf{Strat}_{\text{V}}^{+m} \leftrightarrows \infty\text{-Cat}_{\text{Sat-Ind}}^{+m}: N$$

where $\mathbf{Strat}_{\text{V}}^{+m}$ is the category of $m$-marked simplicial sets equipped with the (saturated) Verity model structure from [43] and [38], which we review in Section 4.4. As explained above, this generalizes the results of the second named author from [32].

## 2 $\infty$-Categories and Marked $\infty$-Categories

### 2.1 $\infty$-Categories

A globular set is a presheaf on the globular category $\mathbb{G}$:

$$\mathbb{D}_0 \xrightarrow[i_0]{i_0^+} \mathbb{D}_1 \xrightarrow[i_1]{i_1^+} \mathbb{D}_2 \xrightarrow[i_2]{i_2^+} \mathbb{D}_3 \xrightarrow[i_3]{i_3^+} \mathbb{D}_4 \dots$$

with the relations $i_n^+ i_{n-1}^\epsilon = i_n^- i_{n-1}^\epsilon$ for any $n > 0$ and $\epsilon \in \{+, -\}$. For any $n > k$ and $\epsilon \in \{+, -\}$, we also denote by $i_k^\epsilon$ the composite $\mathbb{D}_k \xrightarrow{i_k^\epsilon} \mathbb{D}_{k+1} \xrightarrow{f} \mathbb{D}_n$ where $f$ is any map. These and the identity arrows are the only maps in the category $\mathbb{G}$.

**2.1 Notation.** If $X$ is a globular set, one denotes by $X_n$ the set $X(\mathbb{D}_n)$. The map $X_n \rightarrow X_k$ induced by $i_k^\epsilon: \mathbb{D}_k \rightarrow \mathbb{D}_n$ is denoted by $\pi_k^\epsilon$.

**2.2 Definition.** Let $X$ be a globular set and $n$ a positive integer. A $n$-arrow of $X$ is an element of $X_n$.

A *arrow of $X$* is an element of $\prod_{k \geq 0} X_k$. If $a$ is an arrow of $X$, its *dimension* is the integer $n$ such that $a$ belongs to $X_n$.

If $a$ is an $n$-arrow of $X$ and $k$ an integer strictly less than $n$, the $k$-*source of $a$* is the $k$-arrow $\pi_k^-(a)$ and the $k$-*target of $a$* is the $k$-arrow $\pi_k^+(a)$.

**2.3 Definition.** An $\infty$-*category* is a globular set $X$ together with operations of *compositions*

$$X_n \times_{X_k} X_n \rightarrow X_n \quad (0 \leq k < n)$$

which associates to two $n$-arrows $(x, y)$ verifying $\pi_k^+(x) = \pi_k^-(y)$, one $n$-arrow $x \#_k y$, as well as *identities*

$$X_n \rightarrow X_{n+1}$$

associating to an $n$-arrow $x$, an $(n+1)$-arrow $\mathbb{I}_x$, and satisfying the following axioms:

8