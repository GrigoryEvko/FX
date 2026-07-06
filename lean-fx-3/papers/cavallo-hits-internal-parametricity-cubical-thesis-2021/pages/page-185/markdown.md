Bridge types

173

- $IP(\tau) \models \Psi \Vdash \text{Bridge}(\boldsymbol{x}.A, M_0, M_1) \approx \text{Bridge}(\boldsymbol{x}.A, M'_0, M'_1) \downarrow R$ whenever

- $A \approx A' \in \Downarrow \tau[S]$ for some $(\Psi, \boldsymbol{x} : \mathbf{I})$-PER $S$,
- $M_\varepsilon \approx M'_\varepsilon \in \Downarrow S[\varepsilon/x]$ for $\varepsilon \in \{0, 1\}$,
- $V \approx V' \in R\langle \psi \rangle$ holds for $\Psi' \Vdash \psi \in \Psi$ exactly when $V = \lambda^\mathbf{I}x.M$ and $V' = \lambda^\mathbf{I}x.M'$ for some $M, M'$ with $M \approx M' \in \Downarrow S\psi$ and $M[\varepsilon/x] \approx M_\varepsilon\psi \in \Downarrow S\psi[\varepsilon/x]$ for $\varepsilon \in \{0, 1\}$.

- $IP(\tau) \models \Psi \Vdash \text{Gel}_r(A, B, a.b.R) \approx \text{Gel}_r(A', B', a.b.R') \downarrow S$ whenever

- $\tau \models \Psi \Vdash \boldsymbol{r} \in \mathbf{I}$,
- $A \approx A' \in \Downarrow \tau[S]$ for some $(\Psi \setminus \boldsymbol{r})$-PER $S$,
- $B \approx B' \in \Downarrow \tau[T]$ for some $(\Psi \setminus \boldsymbol{r})$-PER $T$,
- $R\psi[M/a, N/b] \approx R'\psi[M'/a, N'/b] \in \Downarrow \tau[U_{M,N}]$ for all $\Psi' \Vdash \psi \in (\Psi \setminus \boldsymbol{r})$, $M \approx M' \in \Downarrow S\psi$, and $N \approx N' \in \Downarrow T\psi$, for some family of PERs $U_{M,N}$ respecting equality in $\Downarrow S$ and $\Downarrow T$,
- $V \approx V' \in S\langle \psi \rangle$ holds for $\Psi' \Vdash \psi \in \Psi$ exactly when one of the following holds:

- $\boldsymbol{r}\psi = \mathbf{0}$, and $V \approx V' \in S\psi$,
- $\boldsymbol{r}\psi = \mathbf{1}$, and $V \approx V' \in T\psi$,
- $\boldsymbol{r}\psi = \boldsymbol{x}$, and $V = \text{gel}_x(M, N, P)$ and $V' = \text{gel}_x(M', N', P')$ with $M \approx M' \in \Downarrow S\psi$, $N \approx N' \in \Downarrow T\psi$, and $P \approx P' \in \Downarrow U_{M,N}\psi$.

We define the candidate type system $\tau_0^{IP}$ to be the least fixed point of $F \cup H \cup IP$, where $F$ is as defined in Example 3.1.32 and $H$ is as defined in Example 6.2.22; we may omit $H$ if we have no interest in interpreting higher inductive types.

As in Examples 3.1.33 and 6.2.23, we may construct a type system for internally parametric type theory with a universe by taking the least fixed point of $F \cup H \cup IP \cup U(\tau_0^{IP})$, where $U$ is as defined in Example 3.1.33.

## 9.2 Bridge types

The first type former we need for parametric type theory is the internalization of bridge interval abstraction: the bridge type. We think of an element of $\text{Bridge}(\boldsymbol{x}.A, M_0, M_1)$ as a proof that $M_0$ and $M_1$ are related across the relation $\boldsymbol{x}.A$.

We display the standard collection of rules for bridge types in Figure 9.2. Like paths, bridges are formed by abstraction and used by application, and they satisfy familiar reduction, boundary, and uniqueness equations. The only distinction is the addition of the interval restriction $\setminus \boldsymbol{r}$ in the application rule, which forbids us from instantiating a