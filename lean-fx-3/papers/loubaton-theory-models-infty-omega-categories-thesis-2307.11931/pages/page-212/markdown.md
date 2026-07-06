CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES---

**4.2.1.63.** A functor $f : C \to D$ is *fully faithful* if for any pair of objects $a, b \in C$, the induced morphism $\hom_C(a, b) \to \hom_D(fa, fb)$ is an equivalence.

**Proposition 4.2.1.64.** *A functor is fully faithful if and only if it has the unique right lifting property against $\{0\} \coprod \{1\} \to \mathbf{D}_n$ for $n > 0$.*

*Proof.* Let $f$ be a functor having the unique right lifting property against $\{0\} \coprod \{1\} \to \mathbf{D}_n$ for $n > 0$. As $[\emptyset, 1] = \{0\} \coprod \{1\}$ and $[\mathbf{D}_n, 1] = \mathbf{D}_{n+1}$, this is equivalent to asking for any pair of objects $c, d$ and for any integer $n$, that $f(c, d)$ has the unique right lifting property against $\emptyset \to \mathbf{D}_n$, which in turn is equivalent to $f$ being fully faithful according to lemma 4.2.1.10. $\square$

**Proposition 4.2.1.65.** *Fully faithful functors are stable under limits.*

*Proof.* This is a consequence of the fact that fully faithful functors are characterized by unique right lifting properties. $\square$

**Lemma 4.2.1.66.** *Let $p : C \to D$ be a fully faithful functor. The induced morphism $C_0 \to D_0$ is a monomorphism.*

*Proof.* To this extent, we have to show that $p : C \to D$ has the unique right lifting property against $1 \coprod 1 \to 1$. This is equivalent to show that $p$ has the unique right lifting property against $\iota : 1 \coprod 1 \to E^{eq}$.

The proposition 4.2.1.64 implies that $p$ as the unique right lifting property against $1 \coprod 1 \to \mathbf{D}_1$ and $1 \coprod 1 \to \mathbf{D}_2$. By left cancellation, this implies that $p$ has the unique right lifting property against $\mathbf{D}_2 \to \mathbf{D}_1$. As $\iota$ is a composition of pushouts along $1 \coprod 1 \to \mathbf{D}_1$ and $\mathbf{D}_2 \to \mathbf{D}_1$, this directly concludes the proof. $\square$

**Proposition 4.2.1.67.** *A morphism $f : C \to D$ is an equivalence if and only if it is fully faithful and induces a surjection on objects.*

*Proof.* This is necessary. Suppose that $f$ is fully faithful. According to 4.2.1.64, for any $n > 0$, $f_n : C_n \to D_n$ is an equivalence. If $f$ induces a surjection on objects, lemma 4.2.1.66 implies that $f_0 : C_0 \to D_0$ is an equivalence. We can then apply proposition 4.2.1.9. $\square$

## 4.2.2 Discrete Conduché functors

**4.2.2.1.** We denote $\nabla_{k,n}$ the unique globular morphism between $\mathbf{D}_n$ and $\mathbf{D}_n \coprod_{\mathbf{D}_k} \mathbf{D}_n$. A morphism $f : C \to D$ between $(\infty, \omega)$-categories is a *discrete Conduché functor* if it has the unique right lifting property against units $\mathbb{I}_{n+1} : \mathbf{D}_{n+1} \to \mathbf{D}_n$ for any integer $n$, and against compositions $\nabla_{k,n} : \mathbf{D}_n \to \mathbf{D}_n \coprod_{\mathbf{D}_k} \mathbf{D}_n$ for any pair of integers $k \leq n$.

202