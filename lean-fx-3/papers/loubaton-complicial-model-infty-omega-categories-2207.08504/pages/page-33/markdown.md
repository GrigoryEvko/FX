1.2. GRAY OPERATIONS

Proof. By lemma 1.2.2.5, there exists a sequence $(b_i)_{i \le n}$ such that $b_0 = b$, $b_n = b'$ and for all $i < n$, $b_i$ and $b_{i+1}$ are 0-composable. The sequence

$$b *_0 b_1 *_0 \dots *_0 b_{n-1} *_0 b'$$

is well defined, and then so is the sequence

$$\pi_1^\alpha b *_0 b_1 *_0 \dots *_0 b_{n-1} *_0 b'.$$

As $\pi_1^\alpha b$ is a 0-composite of $c$ with other elements of $B_1^c$, this concludes the proof.

Lemma 1.2.2.11. Let $r, u$ be two 2-cells of $D$ such that $B_1^u \subset B_1^r$. Let $x$ in $B_2^u$. Then there exists a unique decomposition of $u$ of shape

$$u = v *_1 w *_1 t$$

such that

(1) for any element $b$ in $B_2^v$, $b <_1^r x$;
(2) for any element $b$ in $B_2^t$, $x <_1^r b$;
(3) for any element $b$ in $B_2^w$, $\neg(b <_1^r x) \lor \neg(x <_1^r b)$

If for any element of $b$ in $B_2^u$ different from $x$, $\neg(b <_1^r x) \lor \neg(x <_1^r b)$, then there exists a unique decomposition of $u$ of shape

$$u = v *_0 w *_0 t$$

such that

(1) for any element $b$ in $B_1^v$, $b <_0^r x$;
(2) for any element $b$ in $B_1^t$, $x <_0^r b$;
(3) $w$ is either $x$ or a cell of lower dimension.

Proof. We will construct these two decompositions at the same time. To this extend, we will use the Steiner theory recalled in section 1.2.1.

Let $i$ be either 1 or 0. If $i = 0$, we then suppose furthermore that for any element of $b$ in $B_2^u$ different from $x$, $\neg(b <_1^r x) \lor \neg(x <_1^r b)$. We denote by

$$\left( \begin{array}{ccc} u_0^- & u_1^- & u_2^- \\ u_0^+ & u_1^+ & u_2^+ \end{array} \right)$$

the array corresponding to the cell $u$. For any $i < j \le 2$ and $\alpha \in \{-, +1\}$, we denote

$$\begin{array}{l} v_j^\alpha := \sum \{b \in [u]_j^\alpha, \ b <_i x\} \quad t_j^\alpha := \sum \{b \in [u]_j^\alpha, \ b >_i x\} \\ w_j^\alpha := \sum \{b \in [u]_j^\alpha, \ \neg(b <_j x) \land \neg(b <_j x)\} \end{array}$$

and

$$\begin{array}{lll} v_i^+ := u_i^+ & w_i^+ := v_i^- & t_i^+ := w_i^- \\ v_i^- := u_i^+ - \partial(v_{i+1}^-) & w_i^- := v_i^- - \partial(w_{i+1}^-) & t_i^- := u_i^- \end{array}$$

and for any $j < i$ and $\alpha \in \{-, +1\}$

$$v_j^\alpha := u_j^\alpha \quad w_j^\alpha := u_j^\alpha \quad t_j^\alpha := u_j^\alpha$$

33