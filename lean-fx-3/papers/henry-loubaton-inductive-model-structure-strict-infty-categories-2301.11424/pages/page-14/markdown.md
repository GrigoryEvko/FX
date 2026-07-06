*Proof.* The first equality corresponds to the fact that $X \otimes Y$ is generated under composition by arrows of the form $x \otimes y$, as proven in Lemma 2.14. The second equality corresponds to the fact that arrows of dimension strictly greater than 0 in $X \otimes Y$ are generated under composition by arrows of the form $x \otimes y$ where either $x$ or $y$ has dimension strictly greater than 0, which directly follows from the previous claim, and from the fact that $x \otimes y$ is of dimension strictly greater than 0 if at least one of $x$ or $y$ is. $\square$

**2.24 Lemma.** *Let $X$ be an $\infty$-category and $M, N$ be two subsets of arrows of $X$. Then:*

$$\overline{M \cup N} = \overline{\overline{M} \cup N} = \overline{M \cup \overline{N}} = \overline{\overline{M} \cup \overline{N}}$$

*Proof.* This is straightforward. $\square$

**2.25 Lemma.** *Let $X$ and $Y$ be two $\infty$-categories and $M \subset X_{\geq 0}$ and $N \subset Y_{\geq 0}$. Then:*

$$\overline{M \otimes N} = \overline{\overline{M} \otimes N} = \overline{M \otimes \overline{N}} = \overline{\overline{M} \otimes \overline{N}}$$

*Proof.* We will only show the equality $\overline{M \otimes N} = \overline{\overline{M} \otimes \overline{N}}$. The equality $\overline{M \otimes N} = \overline{\overline{M} \otimes \overline{N}}$ can be proved in the same way, and the last equality follows immediately by applying the result to $M$ and $\overline{N}$.

We will also only prove the results for $m = \infty$; the case of a general $m$ follows immediately as it marks all arrows of dimension strictly greater than $m$ on each side of these equalities.

The evident inclusion $M \subset \overline{M}$ implies $\overline{M \otimes N} \subset \overline{\overline{M} \otimes \overline{N}}$, so it is enough to show that $\overline{M} \otimes N \subset \overline{\overline{M} \otimes \overline{N}}$.

Let $K$ be the set of arrows $k$ in $X$ such that $k \otimes n \in \overline{M \otimes N}$ for all $n \in N$. We need to show that $K$ is closed under identity and composition to finish the proof.

If $k = \mathbb{I}_x$, then $k \otimes n = \mathbb{I}_{x \otimes n} \in \overline{M \otimes N}$. Let now $k, k' \in K$ of dimension $n$ such that $k \#_i k'$ is defined. They are encoded by a map $\mathbb{D}_n \coprod_{\mathbb{D}_n} \mathbb{D}_n \to X$, and let $y \in N$ be an arrow of dimension $m$ in $Y$, encoded by a map $\mathbb{D}_m \to Y$.

Together these induce a map $e: (\mathbb{D}_n \coprod_{\mathbb{D}_n} \mathbb{D}_n) \otimes \mathbb{D}_m \to X \otimes Y$. $(\mathbb{D}_n \coprod_{\mathbb{D}_n} \mathbb{D}_n) \otimes \mathbb{D}_m$ is a polygraph of dimension $m + n$ with only two generating arrows of maximal dimensions that are sent to $k \otimes y$ and $k' \otimes y$, which are by hypothesis in $\overline{M \otimes N}$.

Now the arrow corresponding to $(k \#_i k') \otimes y$ in $(\mathbb{D}_n \coprod_{\mathbb{D}_n} \mathbb{D}_n) \otimes \mathbb{D}_m$ is in $\overline{M \otimes N}$ as all the top-dimensional generators that appear in it are in $\overline{M \otimes N}$. We have proved that $k \#_i k' \otimes y \in \overline{M \otimes N}$ for all $y \in N$, hence $k \#_i k' \in K$ and this concludes the proof. $\square$

**2.26 Lemma.** *Let $X, Y$ be two $\infty$-categories, $M \subset X_{\geq 0}$ and $N \subset Y_{\geq 0}$. Then we have*

$$\begin{array}{rcl} \overline{M \ominus N} & = & \overline{\overline{M} \ominus \overline{N}} \\ \overline{M \ominus N} & = & \overline{\overline{M} \ominus \overline{N}}. \end{array}$$

*Proof.* Given the formula for $M \ominus N$ and $M \ominus N$ from Notation 2.22, this is a direct consequence of Lemma 2.24 and Lemma 2.25. $\square$

14