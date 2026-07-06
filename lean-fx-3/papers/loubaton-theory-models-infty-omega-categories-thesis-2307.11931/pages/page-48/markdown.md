CHAPTER 1. THE CATEGORY OF $(0, \omega)$-CATEGORIES

As the morphism $j$ is degenerate and different of the identity, there exists an integer $k$ and a non trivial $k$-cell $d$ of $b'$ that is sent to an identity by $j$. Now, let $d'$ be a $k$-generator of the polygraph $b$ that appears in the decomposition of $i(d)$. The commutativity of the previous square and the fact that the $(0, \omega)$-categories $a_i$ are polygraphs implies that for any $i$, the $k$-cell $a'$ is sent to an identity by the morphism $b \to a_i$. As for any $i < n$ and any $l \ge k$, there is no non trivial $l$-cell in $a_i$ whose $(k-1)$-source and $(k-1)$-target are the same, this implies that every $l$-cell of $b$ that is $(k-1)$-parallel with $d'$ is send to the identity by the morphism $b \to a_i$.

We denote $\bar{b}$ the globular sum obtained by crushing all $l$-cells of $b$ that are $(k-1)$-parallel with $d'$. The induced degenerate morphism $b \to \bar{b}$ factors all the morphisms $b \to a_i$ which is in contradiction with the fact that $\{b \to a_i\}_{i<n}$ is an element of $\Theta_{/\mathbf{a}}^{\hookrightarrow}$. $\square$

**1.1.3.12.** We say that an element $\{v \to a_i\}_{i<n}$ in the category $\Theta_{/\mathbf{a}}^{\hookrightarrow}$ is of height 0 if $v \to a_0$ factors through $\partial a_0$ or $v \to a_{n-1}$ factors through $\partial a_{n-1}$. The height of an element $w$ is the maximal integer $m$ such that there exists a sequence $v_0 \to v_1 \to \ldots \to v_m = w$ in $\Theta_{/\mathbf{a}}^{\hookrightarrow}$ with $v_i \neq v_{i+1}$ for any $i < m$ and such that $v_0$ is of height 0 and $v_1$ is not. As $\Theta$ is a Reedy category, all elements have finite height.

**Lemma 1.1.3.13.** *For any morphism $p : [b, m] \to i^*[\mathbf{a}, n]$ that preserves extremal objects, there exists a unique integer $k$, a unique element $\{b' \to a_i\}_{i<n}$ of height $k$, and a unique morphism $[f, i] : [b, m] \to [b', n]$ that doesn't factors through $[\partial b', n]$, and such that the induced triangle*

$$\begin{array}{c} [b, m] \xrightarrow{[f, i]} [b', n] \\ \searrow \quad \downarrow_{p'} \\ i^*[\mathbf{a}, n] \end{array}$$

commutes.

*If $\{\tilde{b} \to a_i\}_{i<n}$ is any other object of non negative height, and $[\tilde{f}, j] : [b, m] \to [\tilde{b}, n]$ is a morphism that make the induced triangle*

$$\begin{array}{c} [b, m] \xrightarrow{[\tilde{f}, j]} [\tilde{b}, n] \\ \searrow \quad \downarrow_{\tilde{p}} \\ i^*[\mathbf{a}, n] \end{array}$$

commutative, then $\{\tilde{b} \to a_i\}_{i<n}$ is of height strictly superior to $k$ and $[\tilde{f}, j]$ factors through $[\partial \tilde{b}, n]$.

*Proof.* The lemma 1.1.3.10 implies the first assertion. For the second one, suppose given an object $\{\tilde{b} \to a_i\}_{i<n}$ of non negative height and a morphism $[\tilde{f}, j] : [b, m] \to [\tilde{b}, n]$

38