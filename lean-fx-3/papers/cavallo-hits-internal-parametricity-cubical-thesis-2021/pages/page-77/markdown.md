Cubical computational type theory 65

$M\psi \approx V \in \Downarrow R\psi$. Expanding $\Downarrow R\psi$, we have that $M\psi \Downarrow V_\psi$ for some $V_\psi$ with $V_\psi \approx V \in R\psi$. By value-coherence, we then have $V_\psi \approx V \in \Downarrow R\psi$. It follows by coherent head expansion that $M \approx V \in \Downarrow R$. $\square$

Finally, we have a lemma allowing us to analyze the behavior of “eliminator-like” terms—that evaluate some argument and then do something with its value—in terms of their behavior of values.

**Definition 3.1.37 (Eager terms).** We say that a term $a.N$ depending on one term variable and interval variables in $\Psi$ is *eager* when for every $\Psi' \Vdash \psi \in \Psi$ and term $M$ in $\Psi'$, we have $N\psi[M/a] \Downarrow W$ if and only if there exists some $V$ such that $M \Downarrow V$ and $N\psi[V/a] \Downarrow W$.

**Lemma 3.1.38 (Elimination).** Fix an ambient candidate type system satisfying the unicity and PER conditions. Let $a.N, a.N'$ be eager terms. Suppose we have $\Psi \Vdash A$ pretype and a $(\Psi, a:A)$-PER $S$. Given any sub-relation $R \subseteq [A]$ with the property that $N\psi[V/a] \approx N'\psi[V'/a] \in \Downarrow S\langle\psi, V/a\rangle$ for all $\Psi' \Vdash \psi \in \Psi$ and $V \approx V' \in R\psi$, we have $N\psi[M/a] \approx N'[M'/a] \in \Downarrow S\langle\mathrm{id}_\Psi, M/a\rangle$ for all $M \approx M' \in \Downarrow R$.

*Proof.* Suppose $M \approx M' \in \Downarrow R$, and let $\Psi_1 \Vdash \psi_1 \in \Psi$ and $\Psi_2 \Vdash \psi_2 \in \Psi_1$ be given. Then we have $M\psi_1 \Downarrow V, M'\psi_1 \Downarrow V', M\psi_1\psi_2 \Downarrow V_{12}, M'\psi_1\psi_2 \Downarrow V_{12}', V\psi_2 \Downarrow V_2$, and $V'\psi_2 \Downarrow V_2'$, for some values such that $V_{12}, V_2$ are pairwise related to $V_{12}', V_2'$ by $R\psi_1\psi_2$.

By assumption, we know that $N\psi_1[V/a] \approx N'\psi_1[V'/a] \in \Downarrow S\langle\psi_1, V/a\rangle$. Note that as $[A]$ is value-coherent, we have $\Psi_1 \Vdash M\psi_1 = V \in A\psi_1$ by **Lemma 3.1.36**, thus that $\Downarrow S\langle\psi_1, V/a\rangle = \Downarrow S\langle\psi_1, M\psi_1/a\rangle$. By instantiating with $\mathrm{id}_{\Psi_1}$ and $\psi_2$, we can conclude that $N\psi_1[V/a] \Downarrow W$ and $N'\psi_1[V'/a] \Downarrow W'$ with $P \approx P' \in \Downarrow S\langle\psi_1\psi_2, V\psi_1\psi_2/a\rangle$ for $P \in \{N\psi_1\psi_2[V\psi_2/a], W\psi_2\}$ and $P' \in \{N'\psi_1\psi_2[V'\psi_2/a], W'\psi_2\}$.

Also by assumption, we know that $N\psi_1\psi_2[X/a] \approx N'\psi_1\psi_2[X'/a] \in \Downarrow S\langle\psi_1\psi_2, X/a\rangle$ for $X \in \{V_{12}, V_2\}$ and $X' \in \{V_{12}', V_2'\}$; again, we have $\Downarrow S\langle\psi_1\psi_2, X/a\rangle = \Downarrow S\langle\psi_1\psi_2, M\psi_1\psi_2/a\rangle$ for such $X$. Using the inclusion of $\Downarrow$ in $\Downarrow$, we have in particular that $N\psi_1\psi_2[X/a] \approx N'\psi_1\psi_2[X'/a] \in \Downarrow S\langle\psi_1\psi_2, M\psi_1\psi_2/a\rangle$ for such $X, X'$. Because $a.N, a.N'$ are eager terms, we know that $N\psi_1\psi_2[V_{12}/a]$ has the same value as $N\psi_1\psi_2[M\psi_1\psi_2/a]$ and $N\psi_1\psi_2[V_2/a]$ has the same value as $N\psi_1\psi_2[V\psi_2/a]$; likewise for their primed equivalents. Thus $N\psi_1\psi_2[Q/a] \approx N'\psi_1\psi_2[Q'/a] \in \Downarrow S\langle\psi_1\psi_2, M\psi_1\psi_2/a\rangle$ for $Q \in \{M\psi_1\psi_2, V\psi_2\}$ and $Q' \in \{M'\psi_1\psi_2, V'\psi_2\}$.

Using that $S$ is a PER, we may combine the above to conclude that we have $P \approx P' \in \Downarrow S\langle\psi_1\psi_2, V\psi_1\psi_2/a\rangle$ for $P \in \{N\psi_1\psi_2[M\psi_1\psi_2/a], W\psi_2\}$ and $P' \in \{N\psi_1\psi_2[M'\psi_1\psi_2/a], W'\psi_2\}$, as required. $\square$

### 3.1.6.1 Path types

The first type we consider is the path type, which provides a gentle introduction to reasoning with $\Psi$-relations. None of the operational semantics rules for path types depends on