A relation is said to be well-founded when all its elements are accessible. Note that a well-founded relation need not be transitive.

(2*2) We eventually wish to show that $\prec$ is well-founded but prior to this we must introduce a supplementary well-founded ordering. The well-foundedness of $\prec$ will follow from well-founded induction on this secondary ordering.

Fix a type $X$ and a well-founded relation $\prec : X \times X \to \Omega$ for the remainder of this section. We define a new relation $\sqsubset$ on $\operatorname{List}(X)$:

$$\frac{m \geq 1 \quad \exists f : \{1 \dots n\} \to \{1 \dots m\}. \forall i \leq n. x_i < y_{f(i)}}{[x_1, \dots, x_n] \sqsubset [y_1, \dots, y_m]}$$

We adapt a proof due to Wilfried Buchholz as described by Nipkow [Nip98] to prove that $\sqsubset$ is well-founded.

(2*3) The empty list is \(\sqsubset\)-accessible.
(2*4) If a list is \(\sqsubset\)-accessible, so too is any permutation.
(2*5) Fix \( y: X \). Suppose for all accessible \( l: \operatorname{List}(X) \) and \( x < y \), \( \operatorname{cons}(x, l) \) is accessible. Then for all accessible \( l: \operatorname{List}(X) \), \( \operatorname{cons}(y, l) \) is accessible.

Proof. Fix an accessible $l$ and suppose that $n \sqsubset \operatorname{cons}(y, l)$. By definition, there exists a division of $n$ into $n_l$ and $n_y$ such that $n_l \sqsubset l$ and each element of $n_y$ is dominated by $y$. Because $l$ is accessible, so too is $n_l$. Therefore, $n_y + n_l$ is accessible by induction on the size of $n_y$ and repeated use of the assumption. Because $n$ is a permutation of $n_y + n_l$, we conclude that $n$ is accessible.

(2*6) If $l : \operatorname{List}(X)$ is $\sqsubset$-accessible and $x : X$, then $\operatorname{cons}(x, l)$ is accessible.

Proof. This follows immediately from the (2*5) and $\prec$-induction on $x$.

(2*7) If $\prec$ is well-founded, so too is $\sqsubset$.

Proof. Fix $l : \operatorname{List}(X)$. We argue by induction on $l$ that $l$ is accessible. In the base case apply (2*3) and in the inductive step apply (2*6).

### 3 Well-foundedness of the directed plump ordering

(3*1) Write \(\operatorname{List}^{+}(X)\) for the type of non-empty lists. Given an non-empty list \(l = [u_0, \ldots, u_n]\), write \(\sqcup l\) for \(\sqcup_{i \leq n} u_i\).
(3*2) Given \( l: \operatorname{List}^{+}(\mathrm{W}_{A}B) \), if \( u \leq \sqcup l \) then \( u \) is \( \prec \)-accessible.

Proof. This follows by well-founded induction on the $\sqsubset$-accessibility of $l$; the details are formalized in Agda.

(3*3) The relation $\prec$ is well-founded.

Proof. We must prove that every $u : \mathrm{W}_A B$ is $\prec$-accessible, but this is a consequence of (3*2) setting $l$ to be the singleton list $[u]$; the details are formalized in Agda.

3