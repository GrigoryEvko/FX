66

Cubical type theory

the status of an interval term, with the effect that the proofs are more or less the same as they would be in ordinary Martin-Löf type theory. By the same token, the rules for the existing types of Martin-Löf type theory are easy to reprove in the cubical setting. Of course, we must now also check that each of these types supports coercion and composition.

# **Rule 3.1.39 (Path pretype formation).**

$$\frac{\Psi, x : \mathbb{I} \Vdash A = A' \text{ type} \quad \Psi \Vdash M_0 = M'_0 \in A[0/x] \quad \Psi \Vdash M_1 = M'_1 \in A[1/x]}{\Psi \Vdash \text{Path}(x.A, M_0, M_1) = \text{Path}(x.A', M'_0, M'_1) \text{ pretype}}$$

*Proof.* We aim to apply coherent value introduction, Lemma 3.1.34. For every $\Psi' \Vdash \psi \in \Psi$, we see that $\text{Path}(x.A, M_0, M_1)\psi$ and $\text{Path}(x.A', M'_0, M'_1)\psi$ are values. Moreover, we have $\tau_i \vDash \Psi' \Vdash \text{Path}(x.A, M_0, M_1)\psi \approx \text{Path}(x.A', M'_0, M'_1) \downarrow R\psi$ where the $\Psi$-relation $R$ is defined like so.

$$V \approx V' \in R\langle\psi\rangle \iff \begin{cases} V = \lambda^\mathbb{I}x.M \text{ and } V' = \lambda^\mathbb{I}x.M' \text{ for some } M, M' \\ \text{with } \tau \vDash \Psi', x : \mathbb{I} \Vdash M = M' \in A\psi \text{ and} \\ \tau \vDash \Psi' \Vdash M[\varepsilon/x] = M_\varepsilon\psi \in A\psi[\varepsilon/x] \text{ for each } \varepsilon \in \{0, 1\} \end{cases}$$

This relies on the stability of the judgments under substitution: for all $\Psi' \Vdash \psi \in \Psi$, we have $\Psi', x : \mathbb{I} \Vdash A\psi = A'\psi$ pretype, $\Psi' \Vdash M_0\psi = M'_0\psi \in A\psi[0/x]$, and $\Psi' \Vdash M_1\psi = M'_1\psi \in A\psi[1/x]$.

In other words, we have $\text{Path}(x.A, M_0, M_1)\psi \approx \text{Path}(x.A', M'_0, M'_1)\psi \in \tau_i[R]\psi$ for every $\Psi' \Vdash \psi \in \Psi$. It follows by Lemma 3.1.34 that $\text{Path}(x.A, M_0, M_1) \approx \text{Path}(x.A', M'_0, M'_1) \in \Downarrow \tau_i[R]$, which is to say that $\Psi \Vdash \text{Path}(x.A, M_0, M_1) = \text{Path}(x.A', M'_0, M'_1)$ pretype. $\square$

The above provides one case of type value-coherence, necessary to show $\tau_i$ is a type system: it implies that whenever $\tau_i \vDash \Psi \Vdash \text{Path}(x.A, M_0, M_1)\psi \approx \text{Path}(x.A', M'_0, M'_1)\psi \downarrow R$, we actually have $\Psi \Vdash \text{Path}(x.A, M_0, M_1)\psi = \text{Path}(x.A', M'_0, M'_1)\psi$ pretype.

The introduction rule follows by a similar argument.

# **Rule 3.1.40 (Path introduction).**

$$\frac{\Psi, x : \mathbb{I} \Vdash A \text{ type} \quad \Psi, x : \mathbb{I} \Vdash M \in A}{\Psi \Vdash \lambda^\mathbb{I}x.M = \lambda^\mathbb{I}x.M' \in \text{Path}(x.A, M[0/x], M[1/x])}$$

*Proof.* Once again, we go by Lemma 3.1.34. For every $\Psi' \Vdash \psi \in \Psi$, we have $(\lambda^\mathbb{I}x.M)\psi \approx (\lambda^\mathbb{I}x.M')\psi \in R\psi$, where $R$ is as defined in the proof of Rule 3.1.39, using the stability of our hypotheses under substitution. It therefore follows that $\lambda^\mathbb{I}x.M \approx \lambda x.M' \in \Downarrow R$. $\square$