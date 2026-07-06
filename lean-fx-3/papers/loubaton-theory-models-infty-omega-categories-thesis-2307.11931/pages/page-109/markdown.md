2.4. GLOBULAR EQUIVALENCES

The left hand morphism being an acyclic cofibration according to 2.4.2.2, this diagram admits a lift $h : (\mathbf{D}_{n+1})_t \to C$. The restriction of $h$ to $i_{n+1}^+$ provides a lift in the first diagram. Now, we consider a diagram of shape:

$$\begin{array}{c} \mathbf{D}_n \xrightarrow{g} C \\ \downarrow \qquad \qquad \qquad \downarrow_p \\ (\mathbf{D}_n)_t \longrightarrow D \end{array}$$

with $n > 1$. Let $s, t$ be respectively the $(n - 1)$-source and the $(n - 1)$-target of $g$. Hypotheses imply that $[p(g)]$ is an isomorphism in $\pi_n(s, t, D)$ and because $p$ is a $\mathbf{D}$-equivalence, so is $[g]$. According to lemma 2.4.1.8, this implies that $g$ is thin. There exists then a lifting in the previous diagram. The case $n = 1$ is similar. The morphism $f$ is then a $\mathbf{D}$-trivial fibration.

**Lemma 2.4.2.6.** *Let $p : X \to Y$ be a $\mathbf{D}$-trivial fibration between complicial sets. Then for any $x \in X_0$, the induced fibrations*

$$X_{/x} \to X \times_Y Y_{/p(x)} \quad \text{and} \quad X_{x/} \to X \times_Y Y_{p(x)/}$$

*are $\mathbf{D}$-trivial fibrations.*

*Proof.* We define $\mathbb{P}(p, n)$ to be the statement that $p$ has the right lifting property against

$$\mathbf{D}_n \cup \partial \mathbf{D}_n \star [0] \to \mathbf{D}_{n+1} \star [0] \text{ and } (\mathbf{D}_n)_t \cup \mathbf{D}_n \star [0] \to (\mathbf{D}_n)_t \star [0]$$

and against

$$[0] \stackrel{co}{\star} \partial \mathbf{D}_n \cup \mathbf{D}_n \to [0] \stackrel{co}{\star} \mathbf{D}_{n+1} \text{ and } [0] \star \mathbf{D}_n \cup (\mathbf{D}_n)_t \to [0] \stackrel{co}{\star} (\mathbf{D}_n)_t$$

We then have to show that for any $n$, $\mathbb{P}(p, n)$ holds.

First, it is obvious that each $\mathbf{D}$-equivalence $p$ satisfies $\mathbb{P}(p, 0)$. As $p$ is a fibration, the corollaries 2.3.2.2 and 2.3.2.3 then imply that $\mathbb{P}(p, n + 1)$ is equivalent to $\mathbb{P}(p(a, b), n)$ for any $a, b \in X_0$, where $p(a, b)$ is the induced morphism: $X(a, b) \to Y(p(a), p(b))$.

Using the fact that $p(a, b)$ is a $\mathbf{D}$-trivial fibration as soon as $p$ is, this shows the desired result.

**Lemma 2.4.2.7.** *$\mathbf{D}$-Trivial fibrations between complicial sets have the right lifting property against $\partial[n] \to [n]$.*

*Proof.* Let $C$ be the class of cofibrations having the right lifting property against $\mathbf{D}$-equivalences. The lemma 2.4.2.6 implies that for any $K \to L$ in $C$, the induced morphism:

$$L \cup K \star [0] \to L \star [0]$$

is in $C$. The class $C$ is then closed under Leibniz join. Furthermore, it includes $\partial[1] \to [1]$, and then, by induction, it includes $\partial[n] \to [n]$ for any integer $n$.

99