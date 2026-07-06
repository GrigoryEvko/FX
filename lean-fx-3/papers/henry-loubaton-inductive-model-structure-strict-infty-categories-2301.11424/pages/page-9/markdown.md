(1) $\forall x \in X_n, \pi_n^e(\mathbb{I}_x) = x$.

(2) $\pi_k^-(x\#_ky) = \pi_k^-(x)$ and $\pi_k^+(x\#_ky) = \pi_k^+(y)$ whenever the composition is defined and $k \leqslant n$.

(3) $\pi_k^e(x\#_ky) = \pi_k^e(x)\#_k\pi_k^e(y)$ whenever the composition is defined and $k > n$.

(4) $x\#_k\mathbb{I}_{\pi_k^+x} = x$ and $\mathbb{I}_{\pi_k^-x}\#_kx = x$.

(5) $(x\#_ky)\#_kz = x\#_k(y\#_kz)$ as soon as one of these is defined.

(6) If $k < n$

$$(x\#_ky)\#_k(z\#_kw) = (x\#_kz)\#_k(y\#_kw)$$

when the left-hand side is defined.

A morphism of $\infty$-categories is a map of globular sets commuting with both operations. The category of $\infty$-categories is denoted $\infty$-Cat.

**2.4 Definition.** An $(n+1)$-arrow $c$ in an $\infty$-category is said to be *trivial*, or an *identity arrow*, if there exists an $n$-arrow $d$ such that $c = \mathbb{I}_d$.

**2.5 Example.** By abuse of notation, we also denote $\mathbb{D}_n$ as the $\infty$-category that admits for any $k < n$ only two non-trivial $k$-arrows, denoted $e_k^-$ and $e_k^+$, and a single non-trivial $n$-arrow, denoted $e_n$, satisfying:

$$\begin{array}{l} \pi_l^-(e_k^e) = e_l^- \quad \pi_l^+(e_k^e) = e_l^+ \quad \text{for } l \le k < n \\ \pi_l^-(e_n) = e_l^- \quad \pi_l^+(e_n) = e_l^+ \quad \text{for } l \le n \end{array}$$

The $\infty$-category $\partial\mathbb{D}_n$ is obtained from $\mathbb{D}_n$ by removing the $n$-arrow $e_n$. We thus have a morphism

$$i_n: \partial\mathbb{D}_n \to \mathbb{D}_n.$$

Note that $\partial\mathbb{D}_0 = \emptyset$.

**2.6 Definition.** If $X$ is an $\infty$-category, we define the globular set $\Sigma X$, called the *suspension of $X$*, by the formula

$$(\Sigma X)_0 = \{a, b\}, \quad (\Sigma X)_{n+1} := X_n \cup \{\mathbb{I}^n a, \mathbb{I}^n b\},$$

where $\mathbb{I}_a^n$ (resp. $\mathbb{I}_b^n$) is the $n$-times iterated identity of $a$ (resp. of $b$). Moreover, $\Sigma X$ inherits from $X$ a structure of an $\infty$-category.

Eventually, for an integer $n$, we define the $\infty$-category $\Sigma^n X$, called the *n-suspension of $X$*, as the $n$-times iterated suspension of $X$.

Next, we define the notion of polygraphs, first introduced under the name "computads" by R. Street in [41] for 2-categories, with the general notion being hinted at in [42]. As far as we know, the first formal introduction of polygraphs in the literature is in [37] and independently in [14], where the name "polygraphs" was introduced. Here we will exploit that the category of polygraphs identifies with a (non-full) subcategory of $\infty$-Cat to give a shorter definition. We refer to the references above for a more complete introduction.

9