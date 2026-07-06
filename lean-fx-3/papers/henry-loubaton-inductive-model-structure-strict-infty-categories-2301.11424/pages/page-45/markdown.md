(1) *cofibrant $\infty$-categories are polygraphs.*
(2) *Acyclic fibrations are the morphisms having the left lifting property with respect to the set of morphisms $\{\partial\mathbb{D}_n \to \mathbb{D}_n, n \in \mathbb{N}\}$.*
(3) *Fibrations are the morphisms having the left lifting property with respect to the set of morphisms $\{\mathbb{D}_n \xrightarrow{i_n^*} \mathbb{D}_{n+1} \xrightarrow{k_{n+1}} G_{n+1}, n \in \mathbb{N}\}$.*
(4) *Cofibrations and acyclic cofibrations are morphisms having the right lifting property against, respectively, acyclic fibrations and fibrations..*

*Proof.* This is Theorem 4.39 and 5.3 of [30]. The first point is the main result of [35]. □

**4.24 Definition.** The *coinductive left semi-model structure* on $\infty$-Cat$^{+\infty}$, denoted by $\infty$-Cat$^{+\infty}_{\text{Coind}}$, is the left Bousfield localization of the left semi-model structure on $\infty$-Cat$^{+\infty}_{\text{Sat-Ind}}$ by the set of morphisms:

$$\{(G_n, \vec{\emptyset}) \rightarrow \mathbb{D}_{n-1}^b, n \in \mathbb{N}^*\}$$

**4.25 Remark.** Remark that if we define $\tilde{G}_n := \pi_{n-1}(G_n, \vec{\emptyset})$, the sequence

$$(G_n, \vec{\emptyset}) \xrightarrow{p_n} \tilde{G}_n \xrightarrow{k_n} \mathbb{D}_{n-1}^b$$

is a factorization as a cofibration followed by an acyclic fibration in the inductive left semi-model structure. Using the terminology of [24], we will say that the cofibration $p_n$ represents the morphism $(G_n, \vec{\emptyset}) \rightarrow \mathbb{D}_{n-1}^b$. As we can see in the construction of the left Bousfield localization provided in the proof of Theorem 7.3 of *op cit*, a marked $\infty$-category $X$ is fibrant in the coinductive left semi-model structure if and only if $X$ is fibrant in the inductive left semi-model structure and has the right lifting property against morphisms $k_n$ and iterated homotopy codiagonals of $k_n$ for all $n > 0$.

**4.26 Proposition.** *Let $X$ be a fibrant $\infty$-marked $\infty$-category in the inductive left semi-model structure. Then $X$ is fibrant in the coinductive left semi-model structure if and only if marked arrows are exactly the coinductively invertible arrows of the underlying $\infty$-category.*

*Proof.* Suppose first that $X$ is fibrant in the coinductive left semi-model structure and let $f$ be a coinductively invertible arrow of the underlying $\infty$-category. By Proposition 4.22, this corresponds to a morphism $f: (G_n, \vec{\emptyset}) \rightarrow X$. As remarked in Remark 4.25, $X$ has the right lifting property against $k_n$, which implies that $f$ can be lifted to $\pi_{n-1}(G_n)$. That shows that $f$ is marked. Moreover, Lemma 3.23 states that all marked arrows are coinductively invertible. This shows that marked arrows exactly correspond to coinductively invertible ones.

For the other direction, suppose that $X$ is a marked $\infty$-category, fibrant in the inductive left semi-model structure, whose marked arrows are the coinductively invertible ones. We want to show that $X$ is fibrant in the coinductive left semi-model structure. According to Proposition 4.20, $X$ is fibrant in the nonlocalized left semi-model structure. We then have to show that for all integers $n > 0$, $X$ has the left lifting property against $k_n$ and iterated homotopy

45