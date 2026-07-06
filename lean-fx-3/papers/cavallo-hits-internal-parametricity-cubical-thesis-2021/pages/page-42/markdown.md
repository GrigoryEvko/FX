30

Martin-Löf's type theory

- $F(\tau) \vDash (a : A) \to B \approx (a : A') \to B' \downarrow R$ whenever

- $A \approx A' \in \Downarrow \tau[S]$ for some PER $S$,
- we have a family of value PERs $(T_M)_{M \in \Downarrow S}$ such that for every $M \approx M' \in \Downarrow S$, we have $B[M/a] \approx B'[M'/a] \in \Downarrow \tau[T_M]$ and $T_M = T_{M'}$,
- $V \approx V' \in R$ holds exactly when $V = \lambda a.N$ and $V' = \lambda a.N'$ for some $N, N'$ with $N[M/a] \approx N'[M'/a] \in \Downarrow T_M$ for every $M \approx M' \in \Downarrow S$.

- $F(\tau) \vDash (a : A) \times B \approx (a : A') \times B' \downarrow R$ whenever

- we have $S$ and $(T_M)_{M \in \Downarrow S}$ as in the function type clause,
- $V \approx V' \in R$ holds exactly when $V = \langle M, N \rangle$ and $V' = \langle M', N' \rangle$ for some $M, M', N, N'$ with $M \approx M' \in \Downarrow S$ and $N \approx N' \in \Downarrow T_M$.

- $F(\tau) \vDash \text{Id}(A, M_0, M_1) \approx \text{Id}(A, M'_0, M'_1) \downarrow R$ whenever

- $A \approx A' \in \Downarrow \tau[S]$ for some PER $S$,
- $M_0 \approx M'_0 \in \Downarrow S$,
- $M_1 \approx M'_1 \in \Downarrow S$,
- $V \approx V' \in R$ holds exactly when $V = \text{refl}(M)$ and $V' = \text{refl}(M')$ with $M \approx M' \in \Downarrow S$, $M \approx M_0 \in \Downarrow S$, and $M \approx M_1 \in \Downarrow S$.

- $F(\tau) \vDash \text{Nat} \approx \text{Nat} \downarrow \text{Nat}$, where $\text{Nat}$ is as defined in Example 2.1.24.
- $F(\tau) \vDash \text{Unit} \approx \text{Unit} \downarrow R$ when $V \approx V' \in R$ if and only if $V = V' = \star$.
- $F(\tau) \vDash \text{Void} \approx \text{Void} \downarrow R$ when $R$ is the empty relation.

We define the candidate value type system $\tau_0$ to be the least fixed point of $F$.

**Proposition 2.1.28.** $\tau_0$ is a value type system.

*Proof.* By way of Lemma 2.1.26, as in Example 2.1.24; see [Ang19, Lemma 2.6] for an explicit proof. $\square$

We show below that $\tau_0$ validates standard rules for each of the types included. We may use $\tau_0$ as a stepping stone to construct a type system $\tau_1$ with a universe: the elements of U in $\tau_1$ will be the types of $\tau_0$.

*Example 2.1.29 (Type system with one universe).* We define a monotone operator $U$ on candidate type systems as follows: given $\tau, U(\tau) \vDash V \approx V' \downarrow R$ holds when $V = V' = U$ and $R$ is the relation $W \approx W' \in R \iff \exists S. \tau \vDash W \approx W' \downarrow S$. We define a candidate value type system $\tau_1$ to be the least fixed point of the monotone operator $\tau \mapsto F(\tau) \cup U(\tau_0)$.