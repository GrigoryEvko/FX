2.4. GLOBULAR EQUIVALENCES

**Proposition 2.4.2.5.** Let $p : C \to D$ be a fibration between complicial sets. The morphism $p$ is a **D**-trivial fibration if and only if it is a **D**-equivalence.

*Proof.* If $p$ is a **D**-trivial fibration, it is obvious that it is a **D**-equivalence. For the converse, suppose $p$ is a fibration and a **D**-equivalence, and consider a diagram

$$\begin{array}{c} \partial \mathbf {D} _ {n} \longrightarrow C \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow p \\ \mathbf {D} _ {n} \xrightarrow [ x ]{} D \end{array}$$

As $p$ is a **D**-equivalence this implies that there exists a cell $\overline{x} : \mathbf{D}_n \to C$ together with a marked $(n+1)$-cell $y : p(\overline{x}) \to y$. All this data corresponds to a diagram:

$$\begin{array}{c} \mathbf {D} _ {n} \xrightarrow {\bar {x}} C \\ \Big \downarrow_ {n + 1} \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow p \\ (\mathbf {D} _ {n + 1}) _ {t} \xrightarrow [ y ]{} D \end{array}$$

The left hand morphism being an acyclic cofibration according to 2.4.2.2, this diagram admits a lift $h : (\mathbf{D}_{n+1})_t \to C$. The restriction of $h$ to $i_{n+1}^+$ provides a lift in the first diagram. Now, we consider a diagram of shape:

$$\begin{array}{c} \mathbf {D} _ {n} \xrightarrow {g} C \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow p \\ (\mathbf {D} _ {n}) _ {t} \longrightarrow D \end{array}$$

with $n > 1$. Let $s, t$ be respectively the $(n - 1)$-source and the $(n - 1)$-target of $g$. Hypotheses imply that $[p(g)]$ is an isomorphism in $\pi_n(s, t, D)$ and because $p$ is a **D**-equivalence, so is $[g]$. According to lemma 2.4.1.8, this implies that $g$ is marked. There exists then a lifting in the previous diagram. The case $n = 1$ is similar. The morphism $f$ is then a **D**-trivial fibration. $\square$

**Lemma 2.4.2.6.** Let $p : X \to Y$ be a **D**-trivial fibration between complicial sets. Then for any $x \in X_0$, the induced fibrations

$$X _ { / x } \to X \times _ { Y } Y _ { / p ( x ) } \quad a n d \quad X _ { x / } \to X \times _ { Y } Y _ { p ( x ) / }$$

are **D**-trivial fibrations.

*Proof.* We define $\mathbb{P}(p, n)$ to be the statement that $p$ has the right lifting property against

$$\mathbf {D} _ {n} \cup \partial \mathbf {D} _ {n} \star [ 0 ] \to \mathbf {D} _ {n + 1} \star [ 0 ] \mathrm {a n d} (\mathbf {D} _ {n}) _ {t} \cup \mathbf {D} _ {n} \star [ 0 ] \to (\mathbf {D} _ {n}) _ {t} \star [ 0 ]$$

and against

$$[ 0 ] \stackrel {c o} {\star} \partial \mathbf {D} _ {n} \cup \mathbf {D} _ {n} \to [ 0 ] \stackrel {c o} {\star} \mathbf {D} _ {n + 1} \mathrm {a n d} [ 0 ] \star \mathbf {D} _ {n} \cup (\mathbf {D} _ {n}) _ {t} \to [ 0 ] \stackrel {c o} {\star} (\mathbf {D} _ {n}) _ {t}$$

We then have to show that for any $n$, $\mathbb{P}(p, n)$ holds.

First, it is obvious that each **D**-equivalence $p$ satisfies $\mathbb{P}(p, 0)$. As $p$ is a fibration, the corollaries 2.3.2.2 and 2.3.2.3 then imply that $\mathbb{P}(p, n + 1)$ is equivalent to $\mathbb{P}(p(a, b), n)$ for any $a, b \in X_0$, where $p(a, b)$ is the induced morphism: $X(a, b) \to Y(p(a), p(b))$.

Using the fact that $p(a, b)$ is a **D**-trivial fibration as soon as $p$ is, this shows the desired result. $\square$

89