1.1. BASIC CONSTRUCTIONS

**1.1.1.4.** We say that an $(0, \omega)$-category $X$ is a *polygraph* if it can be constructed from the empty $(0, \omega)$-category by freely adding arrows with specified source and target. That is if $X$ can be obtained as a transfinite composition $\emptyset = X_0 \rightarrow X_1 \rightarrow \cdots \rightarrow X_i \rightarrow \text{colim } X_i = X$ where for each $i$, the map $X_i \rightarrow X_{i+1}$ is a pushout of $\coprod_S \partial \mathbf{D}_n \rightarrow \coprod_S \mathbf{D}_{n+1}$.

An arrow of a polygraph is said to be a *generator* if it is one of the arrows that has been freely added at some stage.

Each cell in a polygraph can be written as an iterated composite of generators or iterated unit of generators (not necessarily in a unique way). For a $n$-cell $f$, the set of generators of dimension $n$ that appear in such an expression (and even the number of times they appear) is the same for all such expressions. As a consequence, a iterated composition of non trivial cells is always non trivial.

**1.1.1.5.** For any subset $S$ of $\mathbb{N}^*$, we define the functor $(\_)^S : \omega\text{-cat} \rightarrow \omega\text{-cat}$ sending a $\omega$-category $C$ to the category $C^S$ such that for any $n$, there is an isomorphism $C_n \rightarrow C_n^S$ that sends every $n$-cell $f$ to a cell $\overline{f}$ fulfilling

$$\pi_{n-1}^-(\overline{f}) = \overline{\pi_{n-1}^+(f)} \quad \pi_{n-1}^+(\overline{f}) = \overline{\pi_{n-1}^-(f)}$$

if $i \in S$ and

$$\pi_{n-1}^-(\overline{f}) = \overline{\pi_{n-1}^-(f)} \quad \pi_{n-1}^+(\overline{f}) = \overline{\pi_{n-1}^+(f)}$$

if $i \notin S$. These functors are called *dualities* as they are inverse of themselves. Even if there are plenty of them, we will be interested in only a few of them. In particular, we have the *odd duality* $(\_)^{op}$, corresponding to the set of odd integer, the *even duality* $(\_)^{co}$, corresponding to the subset of non negative even integer, the *full duality* $(\_)^\circ$, corresponding to $\mathbb{N}^*$ and the *transposition* $(\_)^t$, corresponding to the singleton $\{1\}$. Eventually, we have equivalences

$$((\_)^{co})^{op} \sim (\_)^\circ \sim ((\_)^{op})^{co}.$$

**1.1.1.6.** Let $\text{Psh}(\text{G})_{\bullet,\bullet}$ be the category of globular set with two distinguished points, i.e. of triples $(X, a, b)$ where $a$ and $b$ are elements of $X_0$. Let $[\_, 1] : \text{G} \rightarrow \text{Psh}(\text{G})_{\bullet,\bullet}$ be the functor sending $\mathbf{D}_n$ on $(\mathbf{D}_{n+1}, \{0\}, \{1\})$ and $i_n^\epsilon$ on $i_{n+1}^\epsilon$. This induces a functor $[\_, 1] : \text{Psh}(\text{G}) \rightarrow \text{Psh}(\text{G})$ that we call the *suspension*. We leave it to the reader to check that whenever $C$ has a structure of $\omega$-category, $[C, 1]$ inherits one from it. This functor then induces a functor

$$[\_, 1] : \omega\text{-cat} \rightarrow \omega\text{-cat}$$

that we calls again the *suspension*. Eventually, we denote by $i_0^- : \{0\} \rightarrow [C, 1]$ (resp. $i_0^+ : \{1\} \rightarrow [C, 1]$) the morphism corresponding to the left point (resp. to the right point).

27