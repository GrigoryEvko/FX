3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

of 3.2.4.2, there is a diagram:

$$\begin{array}{c} [[1] \otimes [n-2], 1] \xrightarrow{[1] \otimes [n-2], d^1} [e \star [n-2], 1] \vee [[n-2], 1] \xrightarrow{e \star [n-2], d^2} [e \star [n-2], 1] \\ [d^0 \otimes [n-2], 1] \downarrow \qquad \qquad \qquad \downarrow \delta_{[n-2]} \qquad \qquad \qquad \downarrow \alpha_{[n-2]} \\ [[2] \bar{\otimes} [n-2], 1] \xrightarrow{\epsilon_{[n-2]}} [[n-2], 2] \xleftarrow{} e \star [[n-2], 1] \\ \qquad \qquad \qquad \qquad \qquad \downarrow e \star \pi \qquad \qquad \qquad \downarrow \\ e \star ([e, 1] \vee [[n-2], 1]) \xleftarrow{} e \star [e, 1] \\ \tau_1 \circ e \star \beta_{[n-1]} \downarrow \qquad \qquad \qquad \downarrow \\ [n+1]^1 \xleftarrow{d^3 \circ \dots \circ d^{n+1}} [2]_t \end{array}$$

This implies that $[[2] \bar{\otimes} [n-2], 1] \to [n+1]^k \to ([n+1]^k)_{\mathrm{mk}}$ factors through $[[2] \bar{\otimes} [n-2] \coprod_{d^0 \otimes a} \tau_{n-1}^i ([1] \otimes [n-2]), 1]$. We can then apply lemma 3.2.4.10.

Lemma 3.2.4.19. Let $0 < k < n-1$ be two integers. We denote by $\tau^k$ the projection $[n] \to [n]^k$. We then have

$$(\tau^k \circ \iota_n \circ [d^{k-1}, 1], \tau^k \circ \iota_n \circ [d^{k+1}, 1]) \ge_{n-1} \tau^k \circ \iota_n \circ [d^k, 1]$$

and

$$\tau^{n-1} \circ \iota_n \circ [d^{n-2}, 1] \ge_{n-1} \tau^k \circ \iota_n \circ [d^{n-1}, 1].$$

Proof. By construction, for any $a$, the morphism $[[2] \star a, 1] \to [2] \star [a, 1] \to [2]_t \star [a, 1]$ factors through $[[2]_t \star a, 1]$. By induction, this implies that the composite morphism $[[n-1], 1] \xrightarrow{\iota_n} [n] \to [n]^k$ factors through $[[n-1]^k, 1]$ for any $k < n-1$. This implies the first assertion.

For the second one, note that $[[1], e] \to [2] \to [2]_t$ factors through $[[1]_t, e]$. By induction, this implies that the composite morphism $[[n-1], 1] \xrightarrow{\iota_n} [n] \to [n]^{n-1}$ factors through $[[n-1]^{n-2}, 1]$ which gives the second one.

Proposition 3.2.4.20. For any $0 \le k \le n$, the morphism $([n]^k)' \to ([n]^k)''$ is a weak equivalence.

Proof. The case $k=0$ and $k=n$ are demonstrated in lemma 3.2.4.1. For the case $0 < k < n$, lemmas 3.2.4.17, 3.2.4.18 and 3.2.4.19 imply that if we denote by $\tau_k$ the projection $[n] \to [n]^k$, we have an inequality: $(\tau_k \circ d^{k-1} \circ \iota_{n-1}, \tau_k \circ d^{k+1} \circ \iota_{n-1}) \ge_{n-1} \tau_k \circ d^k \circ \iota_{n-1}$. Together with the proposition 3.2.4.8, this implies that the following square is homotopy cartesian:

$$\begin{array}{c} [n-1] \cup [n-1] \xrightarrow{d^{k+1} \cup d^{k-1}} [n]^k \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ [n-1]_t \cup [n-1]_t \longrightarrow ([n]^k)'' \end{array}$$

The morphism $([n]^k)' \to ([n]^k)''$ is then a weak equivalence.

### 3.2.5 Saturation extensions

Proposition 3.2.5.1. For any $n \ge -1$, the morphism $[n] \star [3]^{eq} \to [n] \star [3]^\sharp$ is an acyclic cofibration.

133