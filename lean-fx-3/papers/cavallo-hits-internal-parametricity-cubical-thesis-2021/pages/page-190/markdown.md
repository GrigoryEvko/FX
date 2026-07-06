178

Parametric cubical type theory

related results.

$$\operatorname{Bridge}(\boldsymbol{x}.(a:A) \rightarrow B, F_0, F_1)$$

$$\stackrel{?}{\simeq}$$

$$(a_0:A[\mathbf{0}/\boldsymbol{x}]) (a_1:A[\mathbf{1}/\boldsymbol{x}]) (p:\operatorname{Bridge}(\boldsymbol{x}.A, a_0, a_1)) \rightarrow \operatorname{Bridge}(\boldsymbol{x}.B[p\boldsymbol{x}/a], F_0 a_0, F_1 a_1)$$

We cannot, however, simply repeat our proof of paths: we have no coercion across bridges. Instead, we will rely here for the first time on the affinity of bridge variables.

We can easily implement the forward direction as in the proof of Lemma 3.2.6: given $q:\operatorname{Bridge}(\boldsymbol{x}.(a:A) \rightarrow B, F_0, F_1)$, we define the function $\lambda a_0.\lambda a_1.\lambda p.\lambda^\mathbf{I}\boldsymbol{x}.(q\boldsymbol{x})(p\boldsymbol{x})$ from bridges in the domain to bridges in the codomain. The difficulty, then, is in the converse. Suppose we are given a function $h$ of the right hand type above. We need to transform this into a path of functions: given $\boldsymbol{x}:\mathbf{I}$ and then $a:A$, we must produce an element of $B$ that is $F_0 a$ when $\boldsymbol{x}=\mathbf{0}$ and $F_1 a$ when $\boldsymbol{x}=\mathbf{1}$. In the proof of Lemma 3.2.6, we used coercion to create a path from $a$ and applied $h$, but we cannot do this now.

Consider the situation where $a:A$ has been instantiated with some closed term $M$. Because $M$ is introduced after $\boldsymbol{x}$, it might use $\boldsymbol{x}$; indeed, we can think of it as a function of $\boldsymbol{x}$. If we could abstract the variable $\boldsymbol{x}$ in $M$, writing $\lambda^\mathbf{I}\boldsymbol{x}.M$, we would have a bridge over $A$, and could take $h(M[\mathbf{0}/\boldsymbol{x}]) (M[\mathbf{1}/\boldsymbol{x}]) (\lambda^\mathbf{I}\boldsymbol{x}.M)\boldsymbol{x}$ as our result. Of course, we cannot literally do so with $a$: the term $\lambda^\mathbf{I}\boldsymbol{x}.a$ is a constant bridge, as $a$ does not mention $\boldsymbol{x}$. As our operational semantics is defined on closed terms, however, we can instead define an auxiliary operator that performs interval abstraction on such terms.

For this purpose, we introduce the extent operator to the operational semantics, as shown in Figure 9.1 and replicated below. We call this operator “extent” because it reveals the extent of a term ($M$ below) in a given direction, a bridge interval term $\boldsymbol{r}$. If $\boldsymbol{r}$ is a constant, then $M$ is simply a point; if $\boldsymbol{r}$ is a variable $\boldsymbol{x}$, then $M$ is one point on a bridge, namely the point at $\boldsymbol{x}$ of the bridge $\lambda^\mathbf{I}\boldsymbol{x}.M$.

$$\overline{\operatorname{extent}_\varepsilon}(M; a_0.N_0, a_1.N_1, a_0.a_1.\overline{a}.\overline{N}) \longmapsto N_\varepsilon[M/a]$$

$$\overline{\operatorname{extent}_\boldsymbol{x}}(M; a_0.N_0, a_1.N_1, a_0.a_1.\overline{a}.\overline{N}) \longmapsto \overline{N}[M[\mathbf{0}/\boldsymbol{x}]/a_0, M[\mathbf{1}/\boldsymbol{x}]/a_1, \lambda^\mathbf{I}\boldsymbol{x}.M/\overline{a}]\boldsymbol{x}$$

Like an eliminator for an inductive type, extent takes a case branch term for each possible value of $\boldsymbol{r}$, the terms $N_0, N_1$, and $\overline{N}$ above. If $\boldsymbol{r}$ is an endpoint constant, we pass $M$—which is just a point—to the corresponding case, per the first reduction rule above. If $\boldsymbol{r}$ is a variable $\boldsymbol{x}$, then we pass the bridge $\lambda^\mathbf{I}\boldsymbol{x}.M$ (and its two endpoints) to the variable case.

The extent operator satisfies the following principles. We have a typing rule as well as reductions for the constant and variable cases.