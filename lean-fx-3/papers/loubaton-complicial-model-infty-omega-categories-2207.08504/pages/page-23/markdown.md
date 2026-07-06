1.1. BASIC CONSTRUCTIONS

$b \to a_i$. As for any $i < n$ and any $l \ge k$, there is no non trivial $l$-cell in $a_i$ whose $(k-1)$-source and $(k-1)$-target are the same, this implies that every $l$-cell of $b$ that is $(k-1)$-parallel with $d'$ is send to the identity by the morphism $b \to a_i$.

We denote $\bar{b}$ the globular sum obtained by crushing all $l$-cells of $b$ that are $(k-1)$-parallel with $d'$. The induced degenerate morphism $b \to \bar{b}$ factors all the morphisms $b \to a_i$ which is in contradiction with the fact that $\{b \to a_i\}_{i<n}$ is an element of $\Theta_{/\mathbf{a}}^{\rightarrow}$.

**Definition 1.1.3.12.** We say that an element $\{v \to a_i\}_{i<n}$ in the category $\Theta_{/\mathbf{a}}^{\rightarrow}$ is of height 0 if $v \to a_0$ factors through $\partial a_0$ or $v \to a_{n-1}$ factors through $\partial a_{n-1}$. The height of an element $w$ is the maximal integer $m$ such that there exists a sequence $v_0 \to v_1 \to \dots \to v_m = w$ in $\Theta_{/\mathbf{a}}^{\rightarrow}$ with $v_i \neq v_{i+1}$ for any $i < m$ and such that $v_0$ is of height 0 and $v_1$ is not. As $\Theta$ is a Reedy category, all elements have finite height.

**Lemma 1.1.3.13.** For any morphism $p : [b, m] \to i^*[\mathbf{a}, n]$ that preserves extremal objects, there exists a unique integer $k$, a unique element $\{b' \to a_i\}_{i<n}$ of height $k$, and a unique morphism $[f, i] : [b, m] \to [b', n]$ that doesn't factors through $[\partial b', n]$, and such that the induced triangle

$$\begin{array}{c} [b, m] \xrightarrow{[f,i]} [b', n] \\ \searrow \quad \downarrow p' \\ i^*[\mathbf{a}, n] \end{array}$$

commutes.

If $\{\bar{b} \to a_i\}_{i<n}$ is any other object of non negative height, and $[\bar{f}, j] : [b, m] \to [\bar{b}, n]$ is a morphism that make the induced triangle

$$\begin{array}{c} [b, m] \xrightarrow{[\bar{f}, j]} [\bar{b}, n] \\ \searrow \quad \downarrow \bar{p} \\ i^*[\mathbf{a}, n] \end{array}$$

commutative, then $\{\bar{b} \to a_i\}_{i<n}$ is of height strictly superior to $k$ and $[\bar{f}, j]$ factors through $[\partial \bar{b}, n]$.

Proof. The lemma 1.1.3.10 implies the first assertion. For the second one, suppose given an object $\{\bar{b} \to a_i\}_{i<n}$ of non negative height and a morphism $[\bar{f}, j] : [b, m] \to [\bar{b}, n]$ fulfilling the desired condition. The bijection (1.1.3.9) directly implies that $j$ is equal to $i$, and the first assertion implies that $\bar{f}$ is non degenerate.

We can then factor $\bar{f} : b \to \bar{b}$ in a degenerate morphism $b \to \bar{b}$ followed by a monomorphism $\bar{b} \to \bar{b}$ which is not the identity. The lemma 1.1.3.11 then implies that $\{\bar{b} \to \bar{b} \to a_i\}_{i<n}$ is an element of $\Theta_{/\mathbf{a}}^{\rightarrow}$. The first assertion then implies that the two morphisms $[b, m] \to [b', n]$ and $[b, m] \to [\bar{b}, n]$ are equals. As the monomorphism $[b', n] = [\bar{b}, n] \to [\bar{b}, n]$ is not the identity, this concludes the proof.

**Lemma 1.1.3.14.** The morphism $i^*[\partial^0 \mathbf{a}, n] \cup i^*[\partial^{n-1} \mathbf{a}, n] \to i^*[\mathbf{a}, n]$ is in $\overline{\mathbf{M}}$, where $\partial^j \mathbf{a}$ corresponds to the sequence $\{a_1, \dots, \partial a_j, \dots, a_n\}$.

Proof. For $k \in \mathbb{N} \cup \{\infty\}$, we define $x_k$ as the smallest sub object of $i^*[\mathbf{a}, n]$ such that for any element of height inferior or equal to $k$ of $\Theta_{/\mathbf{a}}^{\rightarrow}$, the corresponding morphism $[b, n] \to i^*[\mathbf{a}, n]$ factors through $x_k$. In particular we have $x_0 = i^*[\partial^0 \mathbf{a}, n] \cup i^*[\partial^{n-1} \mathbf{a}, n]$, and the lemma 1.1.3.10 implies that $x_\infty = i^*[\mathbf{a}, n]$. We denote $(\Theta_{/\mathbf{a}}^{\rightarrow})_k$ the set of element of $\Theta_{/\mathbf{a}}^{\rightarrow}$ of height $k$.

23