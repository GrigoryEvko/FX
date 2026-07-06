A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

5

**Proposition 1.9.** *Let $\mathcal{D}$ be an $\omega$-category and $n > 0$. Given $a \in \mathcal{D}_n$, we have that $a \in \mathrm{bieq}_n \mathcal{D}$ if and only if there exist $a^L, a^R \in \mathcal{D}_n$ of the form*

$$a^L, a^R : d_{n-1}^+ a \rightarrow d_{n-1}^- a$$

*and $c, c' \in \mathrm{bieq}_{n+1} \mathcal{D}$ of the form*

$$c : a^L \begin{matrix} * \\ n-1 \end{matrix} a \rightarrow \mathrm{id}_{d_{n-1}^- a} \quad \text{and} \quad c' : a \begin{matrix} * \\ n-1 \end{matrix} a^R \rightarrow \mathrm{id}_{d_{n-1}^+ a}.$$

*Proof.* For the forward direction, we suppose that $a \in \mathrm{bieq} \mathcal{D}$. By Definition 1.7 there exists a bi-invertibility set $E$ containing $a$, and by Definition 1.6 there exist $a^L, a^R \in \mathcal{D}_n$, and $c, c' \in E_{n+1}$ of the form displayed in Definition 1.6. Since $c, c' \in E$, by Definition 1.7 it follows that $c, c' \in \mathrm{bieq}_n \mathcal{D}$, as desired.

For the converse direction, suppose that for a given $a \in \mathcal{D}_n$ there exist $a^L, a^R \in \mathcal{D}_n$, $c, c' \in \mathrm{bieq}_{n+1} \mathcal{D}$ satisfying the conditions of the statement. By Definition 1.7 there exist bi-invertibility sets $E$ and $E'$ in $\mathcal{D}$ containing $c$ and $c'$, respectively. Then $E'' := \{a\} \cup E \cup E'$ is by Definition 1.6 an invertibility set containing $a$. By Definition 1.7, it follows that $a \in \mathrm{bieq}_n \mathcal{D}$, as desired. $\square$

We now establish some closure properties of the set of biequivalences in an $\omega$-category $\mathcal{D}$, which are essentially the content of [Ric20, Theorem 13].

**Lemma 1.10.** *Let $\mathcal{D}$ be an $\omega$-category. If we denote*

$$\mathrm{id}_n \mathcal{D} := \{\mathrm{id}_a \in \mathcal{D}_n \mid a \in \mathcal{D}_{n-k}, \ k > 0\},$$

*the set $\mathrm{id} \mathcal{D} := \coprod_{n>0} \mathrm{id} \mathcal{D}$ is a bi-invertibility set.*

*Proof.* This is straightforward from Definition 1.6. $\square$

**Proposition 1.11.** *Let $\mathcal{D}$ be an $\omega$-category and $n \geq 0$. Given $a \in \mathcal{D}_n$, we have that $\mathrm{id}_a \in \mathrm{bieq}_{n+1} \mathcal{D}$.*

*Proof.* A bi-invertibility set in the sense of Definition 1.6 containing $\mathrm{id}_a$ is constructed in Lemma 1.10. It follows from Definition 1.7 that $\mathrm{id}_a \in \mathrm{bieq}_{n+1} \mathcal{D}$, as desired. $\square$

**Lemma 1.12.** *Let $\mathcal{D}$ be an $\omega$-category. If we denote*

$$E_n := \{b *_k a \mid a, b \in \mathrm{bieq}_n \mathcal{D}, \ 0 \leq k < n-1\},$$

*the set $E := \coprod_{n>0} E_n$ is a bi-invertibility set.*

*Proof.* Given $e := b *_k a \in E_n$, by Proposition 1.9 there exist $a^L, a^R, b^L, b^R \in \mathcal{D}_n$, $c, c', d, d' \in \mathrm{bieq}_{n+1} \mathcal{D}$ of the form

$$c : a^L \begin{matrix} * \\ n-1 \end{matrix} a \rightarrow \mathrm{id}_{d_{n-1}^- a} \quad \text{and} \quad c' : a \begin{matrix} * \\ n-1 \end{matrix} a^R \rightarrow \mathrm{id}_{d_{n-1}^+ a},$$

$$d : b^L \begin{matrix} * \\ n-1 \end{matrix} b \rightarrow \mathrm{id}_{d_{n-1}^- b} \quad \text{and} \quad d' : b \begin{matrix} * \\ n-1 \end{matrix} b^R \rightarrow \mathrm{id}_{d_{n-1}^+ b}.$$

We then define $e^R := b^R *_k a^R \in \mathcal{D}_n$ and $e^L := b^L *_k a^L \in \mathcal{D}_n$, and we set $\ell \in \mathcal{D}_{n+1}$ and $\ell' \in \mathcal{D}_{n+1}$ to be the composites

$$\ell := d \begin{matrix} * \\ k \end{matrix} c : e^L \begin{matrix} * \\ n-1 \end{matrix} e \rightarrow \mathrm{id}_{d_{n-1}^- e} \quad \text{and} \quad \ell' := d' \begin{matrix} * \\ k \end{matrix} c' : e \begin{matrix} * \\ n-1 \end{matrix} e^R \rightarrow \mathrm{id}_{d_{n-1}^+ e}.$$

These composites do make sense because various relations, such as an instance of the interchange law

$$e \begin{matrix} * \\ n-1 \end{matrix} e^R = (b *_k a) \begin{matrix} * \\ n-1 \end{matrix} (b^R *_k a^R) = (b \begin{matrix} * \\ n-1 \end{matrix} b^R) \begin{matrix} * \\ k \end{matrix} (a \begin{matrix} * \\ n-1 \end{matrix} a^R)$$