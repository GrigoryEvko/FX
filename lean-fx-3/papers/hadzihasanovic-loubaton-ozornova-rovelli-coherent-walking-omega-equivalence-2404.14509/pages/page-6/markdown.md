6

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

hold. By definition we see that $\ell \in E_{n+1}$ and $\ell' \in E_{n+1}$, so it follows that $E$ is a bi-invertibility set containing $e$, as desired. $\square$

**Proposition 1.13.** *Let $\mathcal{D}$ be an $\omega$-category and $0 \leq k < n-1$. Given $a, b \in \mathrm{bieq}_n \mathcal{D}$ such that $b *_k a$ is defined, we have that $b *_k a \in \mathrm{bieq}_n \mathcal{D}$.*

*Proof.* A bi-invertibility set in the sense of Definition 1.6 containing $b *_k a$ is constructed in Lemma 1.12. It follows from Definition 1.7 that $b *_k a \in \mathrm{bieq}_n \mathcal{D}$, as desired. $\square$

**Lemma 1.14.** *Let $\mathcal{D}$ be an $\omega$-category. If we denote*

$$E_n := \{b_{n-1} * a \in \mathcal{D}_n \mid a, b \in \mathrm{bieq}_n \mathcal{D}\},$$

*the set $E := \coprod_{n>0} E_n$ is a bi-invertibility set.*

*Proof.* Given $e := b *_{n-1} a \in E_n$, by Proposition 1.9 there exist $a^L, a^R, b^L, b^R \in \mathcal{D}_n$ and $c, c', d, d' \in \mathrm{bieq}_{n+1} \mathcal{D}$ of the form

$$c \colon a^L *_{n-1} a \to \mathrm{id}_{d_{n-1}^- a} \quad \text{and} \quad c' \colon a *_{n-1} a^R \to \mathrm{id}_{d_{n-1}^+ a};$$

$$d \colon b^L *_{n-1} b \to \mathrm{id}_{d_{n-1}^- b} \quad \text{and} \quad d' \colon b *_{n-1} b^R \to \mathrm{id}_{d_{n-1}^+ b}.$$

We then define $e^L := a^L *_{n-1} b^L \in \mathcal{D}_n$ and $e^R := a^R *_{n-1} b^R \in \mathcal{D}_n$, and set $\ell \in \mathcal{D}_{n+1}$ and $\ell' \in \mathcal{D}_{n+1}$ to be the composites

$$\ell := c *_{n} (\mathrm{id}_{a^L *_{n-1}} d *_{n-1} \mathrm{id}_a) \colon e^L *_{n-1} e \to \mathrm{id}_{d_{n-1}^- e}$$

$$\ell' := d' *_{n} (\mathrm{id}_b *_{n-1} c' *_{n-1} \mathrm{id}_{b^R}) \colon e *_{n-1} e^R \to \mathrm{id}_{d_{n-1}^+ e}.$$

These composites do make sense because composition is associative and various relations, such as $d_{n-1}^- a = d_{n-1}^- e$, hold. By Propositions 1.11 and 1.13 we can recognize that $\ell$ and $\ell'$ are composites of $\omega$-bi-equivalences of dimension $n+1$ along cells of dimension $n$, so by definition of $E$ we obtain that $\ell, \ell' \in E_{n+1}$. So $E$ is a bi-invertibility set containing $e$, as desired. $\square$

**Proposition 1.15.** *Let $\mathcal{D}$ be an $\omega$-category and $n > 0$. Given $a, b \in \mathrm{bieq}_n \mathcal{D}$ such that $b *_{n-1} a \in \mathcal{D}_n$, we have that $b *_{n-1} a \in \mathrm{bieq}_n \mathcal{D}$.*

*Proof.* A bi-invertibility set in the sense of Definition 1.6 containing $b *_{n-1} a$ is constructed in Lemma 1.14. It follows from Definition 1.7 that $b *_{n-1} a \in \mathrm{bieq}_n \mathcal{D}$, as desired. $\square$

**Lemma 1.16.** *Let $\mathcal{D}$ be an $\omega$-category. If we denote*

$$E_n := \{b *_{n-1} a^L \in \mathcal{D}_n \mid a, b \in \mathrm{bieq}_n \mathcal{D}, a^L \text{ is a left inverse for } a\},$$

*then the set $E := \coprod_{n>0} E_n$ is a bi-invertibility set.*

*Proof.* Given $e := b *_{n-1} a^L \in E_n$ for $a, b \in \mathrm{bieq}_n \mathcal{D}$, by Proposition 1.9 there exist $a^R, b^L, b^R \in \mathcal{D}_n$ and $c, c', d, d' \in \mathrm{bieq}_{n+1} \mathcal{D}$ of the form

$$c \colon a^L *_{n-1} a \to \mathrm{id}_{d_{n-1}^- a} \quad \text{and} \quad c' \colon a *_{n-1} a^R \to \mathrm{id}_{d_{n-1}^+ a},$$

$$d \colon b^L *_{n-1} b \to \mathrm{id}_{d_{n-1}^- b} \quad \text{and} \quad d' \colon b *_{n-1} b^R \to \mathrm{id}_{d_{n-1}^+ b}.$$