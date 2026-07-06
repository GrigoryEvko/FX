**3.21 Lemma.** *Let $C$ be an $m$-marked $\infty$-category such that all equations have solutions in $C$ and whenever $a$ and $c: a \rightarrow b$ are marked, so is $b$. Then $C$ has the right lifting property against all equations and saturations.*

*Proof.* By definition, $C$ has the right lifting property against all equations. Let $\Omega Q \rightarrow Q$ be a saturation, and let $n$, $x$, and $y$ be the integer and the two generators of Definition 3.4. We denote by $P$ the $m$-marked polygraph obtained from $Q$ by unmarking $x$ and all the $n$-arrows appearing in the $n$-target of $y$. We also denote by $\Lambda P$ the $m$-marked sub-polygraph of $P$ that contains all generators except $x$ and $y$. The morphism $\Lambda P \rightarrow P$ is then an equation.

Suppose now that we have a morphism $f: \Omega Q \rightarrow C$. This corresponds to a solution $(x, y)$ of the equation $\Lambda P \rightarrow P$. We then know that there exists another solution $(\bar{x}, \bar{y})$ of the equation where $\bar{x}$ is marked. Furthermore, as $P \prod_{\Lambda P} P \rightarrow \text{Uni}_{\Lambda P}^{\text{coh}}(P)$ is an equation, it has solutions in $C$, and there exists a marked arrow $z': \bar{x} \rightarrow x$. By assumption, this implies that $x$ is marked. This shows that we can lift the morphism $f$ to $Q$. $\square$

**3.22 Lemma.** *Fibrant objects have the right lifting property against the equations $\mathbf{eq}_{n,n}^{\diamond \cdots}$ and saturations $\mathbf{sat}_{n,n}^{\diamond \cdots}$.*

*Proof.* Consider a lifting problem of $\mathbf{eq}_{n,n}^{\diamond \cdots}$ against $C$. This means that we have in $C$ an $n$-arrow $b$ and a marked $n$-arrow $a$ that share the same source.

Since $C$ is fibrant, it has, by definition, the right lifting property against $\mathbf{eq}_n^{\square}$ as in Construction 3.5. Using the same notations as in 3.5 for the generators of $\Lambda \mathbf{Eq}_n^{\square}$, we choose the image of $a_l$ in $C$ to be an identity for all $l < n$, and $a_n = a$. This gives us a span:

$$\begin{array}{c} \Lambda \mathbf{Eq}_n^{\square} \longrightarrow C \\ \mathbf{eq}_n^{\square} \downarrow \\ \mathbf{Eq}_n^{\square} \end{array}$$

which has a dotted diagonal filling $(x, y)$. But this pair verifies $y: x \#_{k-1} a \rightarrow b$, and is thus a solution to the lifting problem above.

The proof for the saturation $\mathbf{sat}_{n,n}^{\diamond \cdots}$ is similar. $\square$

**3.23 Lemma.** *In a fibrant $m$-marked $\infty$-category, all marked arrows are invertible. Moreover, their inverses are marked.*

*Proof.* Lemma 3.22 states that $C$ has the right lifting property against $\mathbf{eq}_{n,n}^{\diamond \cdots}$ and $\mathbf{sat}_{n,n}^{\diamond \cdots}$.

First, the right lifting property against $\mathbf{eq}_{n,n}^{\diamond \cdots}$ shows that for any marked arrow $a$, there exists a pair $(a^{-1}, \nu)$ where $\nu$ is marked and

$$\nu: a^{-1} \#_n a \rightarrow \mathbb{I}.$$

The fact that $a^{-1}$ is marked follows from the right lifting property against $\mathbf{sat}_{n,n}^{\diamond \cdots}$.

29