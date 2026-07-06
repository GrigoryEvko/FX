the context $\Gamma$, in mode $m$.

The typing rules closely correspond to the rules of the logic in Fig. 1. For example, we have replaced conjunction $\wedge$ by the Cartesian product $\times$. We may construct a proof $(M, N)$ of $A \times B$ by pairing together a proof $M$ of $A$ and $N$ of $B$. Hence, the Curry-Howard correspondence is readily apparent.

One subtle point is that the terms for the introduction of an implication, the elimination of a disjunction, and the elimination of modal term all create *bound variables*. For example, the variable $x$ is bound in the subterm $Q$ within $\text{case}(M; x_A, P; y_B, Q)$. Similarly, the variable $x$ is bound in $N$ within $\text{let}_\mu \text{mod}_\nu(x_A) \leftarrow M$ in $N$. Thus, the usual rules of capture avoidance need to be employed.

## 5.1. Metatheory

We have the following metatheoretic results on the term assignment system.

It is also worth noting that any metatheorem we establish about this system is also a metatheorem about the logic given in Fig. 1: all we have to do is *erase* the new ingredients (terms, variables, and so on). Thus, the theorems established in this section directly correspond to the claims in §3.5.

**Theorem 5.1** (Structural rules). *The following rules are admissible.*

$$\frac{\begin{array}{c} \text{VARWK} \\ \Gamma, x : (\mu \mid A), \Delta \text{ ctx } @ p \quad \Gamma, \Delta \vdash M : C @ p \\ \hline \Gamma, x : (\mu \mid A), \Delta \vdash M : C @ p \end{array}}{\text{VARWK}}$$

$$\frac{\begin{array}{c} \text{EXCH} \\ \Gamma, x : (\mu \mid A), y : (\nu \mid B), \Delta \vdash M : C @ p \\ \hline \Gamma, y : (\nu \mid B), x : (\mu \mid A), \Delta \vdash M : C @ p \end{array}}{\text{EXCH}}$$

*Proof.* By induction on the derivation of the premises.

As discussed in §3.5, we cannot be cavalier with adding locks to the context. The following rule describes how to weaken already extant locks. Given a 2-cell $\alpha$ and two (disjoint) pre-contexts $\Gamma$ and $\Delta$, we define the *partial* metatheoretic operation

$$M[\Gamma; \alpha; \Delta]$$

by the following clauses:

$$\begin{aligned} x^{\alpha'}[\Gamma, x : (\rho \mid A), \Gamma'; \alpha; \Delta] &\stackrel{\text{def}}{=} x^{(1_{\text{locks}(\Gamma')} * \alpha * 1_{\text{locks}(\Delta)}) \circ \alpha'} \\ x^{\alpha'}[\Gamma; \alpha; \Delta, x : (\rho \mid A), \Delta'] &\stackrel{\text{def}}{=} x^{\alpha'} \\ (\lambda x : (\xi \mid A), M)[\Gamma; \alpha; \Delta] &\stackrel{\text{def}}{=} \lambda x : (\xi \mid A), M[\Gamma; \alpha; \Delta, x : (\xi \mid A)] \\ (M(N)_\xi)[\Gamma; \alpha; \Delta] &\stackrel{\text{def}}{=} (M[\Gamma; \alpha; \Delta])(N[\Gamma; \alpha; \Delta, \text{🚆}_\xi])_\xi \\ \text{mod}_\xi(M)[\Gamma; \alpha; \Delta] &\stackrel{\text{def}}{=} \text{mod}_\xi(M[\Gamma; \alpha; \Delta, \text{🚆}_\xi]) \end{aligned}$$

22