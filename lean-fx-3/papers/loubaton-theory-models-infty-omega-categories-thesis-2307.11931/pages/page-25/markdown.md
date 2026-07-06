the unique right lifting property against units $\mathbb{I}_{n+1} : \mathbf{D}_{n+1} \rightarrow \mathbf{D}_n$ for any integer $n$, and against compositions $\nabla_{k,n} : \mathbf{D}_n \rightarrow \mathbf{D}_n \coprod_{\mathbf{D}_k} \mathbf{D}_n$ for any pair of integers $k \leq n$. This notion was originally defined and studied in the context of strict $\omega$-category by Guetta in [Gue18].

**Theorem 4.2.2.9.** *Let $f : C \rightarrow D$ be a discrete Conduché functor. The pullback functor $f^* : (\infty, \omega)\text{-cat}_{/D} \rightarrow (\infty, \omega)\text{-cat}_{/C}$ preserves colimits.*

In the third section, we study Gray operations for $(\infty, \omega)$-categories. We conclude this chapter by proving results of strictification. In particular, we demonstrate the following theorem:

**Theorem 4.3.3.19.** *Let $C$ be an $(\infty, \omega)$-category, $b$ a globular sum, and $f : b \rightarrow C$ any morphism. The $(\infty, \omega)$-categories*

$$1 \stackrel{co}{\star} b \coprod_b C, \quad C \coprod_b b \otimes [1] \quad \text{and} \quad C \coprod_b b \star 1$$

*are strict whenever $C$ is.*

We will also prove the following theorem:

**Theorem 4.3.3.26.** *If $C$ is strict, so are $C \star 1$, $1 \stackrel{co}{\star} C$ and $C \otimes [1]$.*

In the process, we will demonstrate another fundamental equation combining $C \otimes [1]$, $1 \stackrel{co}{\star} C$, $C \star 1$, and $[C, 1]$.

**Theorem 4.3.3.25.** *Let $C$ be an $(\infty, \omega)$-category. The five squares appearing in the following canonical diagram are both cartesian and cocartesian:*

$$\begin{array}{ccc} & C \otimes \{0\} & \longrightarrow & 1 \\ & \downarrow & & \downarrow \\ C \otimes \{1\} & \longrightarrow & C \otimes [1] & \longrightarrow & C \star 1 \\ \downarrow & & \downarrow & & \downarrow \\ 1 & \longrightarrow & 1 \stackrel{co}{\star} C & \longrightarrow & [C, 1] \end{array}$$

*where $[C, 1]$ is the suspension of $C$.*

**Chapter 5.** This chapter is dedicated to the study of *marked* $(\infty, \omega)$-categories, which are pairs $(C, tC)$, where $C$ is an $(\infty, \omega)$-category and $tC := (tC_n)_{n>0}$ is a sequence of full sub $\infty$-groupoids of $C_n$ that include identities and are stable under composition and whiskering with (possibly unmarked) cells of lower dimensions. There are two canonical

15