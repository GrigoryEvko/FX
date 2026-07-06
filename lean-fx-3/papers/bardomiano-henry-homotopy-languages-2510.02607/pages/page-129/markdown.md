1. Every derived type judgment of $U(\mathcal{C})$ is of the form

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \overline{A_\lambda}(t_\alpha)_{\alpha < \lambda} \text{ Type}$$

for some object $A_\lambda$ of $\mathcal{C}$ where for $\alpha \leq \lambda$ the rule

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash t_\alpha : \overline{A_\alpha}[t_\delta \mid x_\delta]_{\delta < \alpha}$$

is a derived rule of $U(\mathcal{C})$.

2. Every type element judgment of $U(\mathcal{C})$ is of the form

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash x_\beta : \Omega_\beta$$

for some $\beta < \mu$, or is of the form

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \overline{f}(t_\alpha)_{\alpha < \lambda} : \Omega$$

for some map $f : A_\lambda \rightarrow B_\mu$ of $\mathcal{C}$ such that for each $\alpha < \lambda$ the rules

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash t_\alpha : \overline{A_\alpha}[t_\delta \mid x_\delta]_{\delta < \alpha}$$

and

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \overline{B_\mu}(t_\beta)_{\beta < \mu} \equiv \Omega$$

are derived rules of $U(\mathcal{C})$.

We may assume that $\mu = \nu + 1$, the limit case will follow by induction. Let $\mathcal{R}_\mathcal{C}$ be the set of type and element type judgments of $U(\mathcal{C})$. Next, we define $\mathcal{J} : \mathcal{R}_\mathcal{C} \rightarrow \mathcal{C}$ inductively. First we get maps:

1. A rule $r_{\Omega_\mu} := \{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \Omega_\mu$ is sent an object $\mathcal{J}(r_{\Omega_\mu}) \in \mathcal{C}$.
2. For any $\alpha < \lambda$ the judgment $r_{t_\alpha} := \{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash t_\alpha : \overline{A_\alpha}[t_\delta \mid x_\delta]_{\delta < \alpha}$ is sent to a map $\mathcal{J}(r_{t_\alpha})$.

The we can make the following definitions:

1. $\mathcal{J}(r_{A_\mu}) := (\mathcal{J}(t_\alpha)_{\alpha < \lambda})^* A_\mu$,
where $\mathcal{J}(t_\alpha)_{\alpha < \lambda}$ denotes the pullbacks as in theorem B.11.
2. $\mathcal{J}(\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \overline{f}(t_\alpha)_{\alpha < \lambda} : \Omega) := (\mathcal{J}(t_\alpha)_{\alpha < \lambda})^* \delta_f^\nu$.
3. $\mathcal{J}(\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash x_\beta : \Omega_\beta) := \delta_{p_\beta}^\beta$ where $p_\beta : \mathcal{J}(r_{\Omega_\mu}) \rightarrow \mathcal{J}(r_{\Omega_\beta})$.

129