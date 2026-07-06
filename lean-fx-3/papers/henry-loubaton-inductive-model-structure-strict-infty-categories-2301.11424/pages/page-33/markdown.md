### 3.4 Equivalences

We now turn to the characterization of weak equivalences between fibrant objects.

**3.32 Definition.** A morphism $p: X \rightarrow Y$ between fibrant $m$-marked $\infty$-categories is an *equivalence of $m$-marked $\infty$-categories* if:

1. (1) For any arrow $x \in X$, if $p(x)$ is marked in $Y$, then $x$ is marked in $X$.
2. (2) For any object $c \in Y$, there exists an object $\tilde{c} \in X$ and a marked arrow $e: p(\tilde{c}) \rightarrow c$.
3. (3) For any pair of parallel arrows $(a, b)$ in $X$, and any arrow $c: p(a) \rightarrow p(b)$ in $Y$, there exists an arrow $\tilde{c}: a \rightarrow b$ in $X$ and a marked arrow $e: p(\tilde{c}) \rightarrow c$ in $X$.

So informally, a functor is an equivalence if it is conservative, essentially surjective, and “essentially surjective on each Hom $\infty$-category”.

**3.33 Proposition.** A morphism $f: X \rightarrow Y$ between fibrant objects in $\infty$-Cat$^{+m}$ is a weak equivalence in the left semi-model structure of Theorem 2.43 if and only if it is an equivalence in the sense of Definition 3.32.

*Proof.* We will use the characterization of weak equivalences between fibrant objects given in Proposition A.7. We recall that in our left semi-model structure, the generating cofibrations are given by

$$I^\partial = \{i_n: \partial \mathbb{D}_n \rightarrow \mathbb{D}_n \mid n \geqslant 0\} \quad I^{+m} = \{\mathbb{D}_n \rightarrow (\mathbb{D}_n, \overline{\{e_n\}}) \mid n \geqslant 0\}$$

To express the homotopy right lifting property, we need a relative cylinder object for each of these cofibrations.

For a map of the form $\mathbb{D}_n \rightarrow (\mathbb{D}_n, \overline{\{e_n\}})$, we have that the canonical map

$$(\mathbb{D}_n, \overline{\{e_n\}}) \prod_{\mathbb{D}_n} (\mathbb{D}_n, \overline{\{e_n\}}) \rightarrow (\mathbb{D}_n, \overline{\{e_n\}})$$

is an isomorphism, so $(\mathbb{D}_n, \overline{\{e_n\}})$ is already a cylinder object. In particular, the weak left lifting property against these maps is exactly the same as the ordinary left lifting property and it corresponds exactly to the first condition of Definition 3.32.

For the map $i_n: \partial \mathbb{D}_n \rightarrow \mathbb{D}_n$, one obtains a relative cylinder object by considering the factorization:

$$\mathbb{D}_n \prod_{\partial \mathbb{D}_n} \mathbb{D}_n \mapsto (\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}}) \rightarrow \mathbb{D}_n$$

The first map freely adds a (marked) $(n+1)$-arrow between the two non-trivial arrows of the domain, so it is a cofibration. And one of the two maps $\mathbb{D}_n \rightarrow (\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}})$ was shown to be an anodyne cofibration in Lemma 2.46, hence proving that this is a relative cylinder object for this cofibration. Using this cylinder to express the weak lifting property against $i_n$, one obtains exactly the second condition (for $n = 0$) and the third condition (for $n > 0$) of

33