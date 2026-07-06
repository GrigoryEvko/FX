1. if $U \leqslant V$ then any $W$ appearing in the supremum defining $\tau(U)$ also appears in the one defining $\tau(V)$ with the same $V'$ and $q$. Hence $\tau$ is order preserving.

2.

$$\tau(V_1) \wedge \tau(V_2) = \bigvee W_1 \wedge W_2$$

where the union runs over all $W_1, W_2 \in A$ such that there exist $q'_1, q'_2$ positive rational numbers, and $V'_1, V'_2 \in B$ such that

$$\delta(W_i) < q'_i;$$

$$V'_i \triangleleft_{q'_i} V_i;$$

$$(W_i, V'_i).$$

For any such $W_1$ and $W_2$ there exists a positive rational number $\epsilon$ such that $\delta(W_i) < q'_i - \epsilon$. Let $q_i = q'_i - \epsilon$. One has in particular $\delta(W_i) < q_i$ and

$$V'_i \triangleleft_{q_i} B_{q_i} V'_i \triangleleft_\epsilon V_i.$$

Moreover $W_1 \wedge W_2$ can be written as the union of $\tau \in A$ such that $\tau \leqslant W_1 \wedge W_2$ and $\delta(\tau) < \epsilon$. Finally, one can apply (MM5) (taking $B_{q_i} V'_i$ instead of $V_i$) to obtain that there exists $V$ such that

$$V \leqslant (B_{q_1} V'_1 \wedge B_{q_2} V'_2) \triangleleft_\epsilon V_1 \wedge V_2$$

and

$$(\tau, V).$$

This proves that $\tau \leqslant \tau(B_\epsilon V)$ with $B_\epsilon B \leqslant V_1 \wedge V_2$ and $B_\epsilon V \in B$ because $B$ is metric, and hence concludes the proof that.

$$\tau(V_1) \wedge \tau(V_2) \leqslant \bigvee_{\substack{V \in B \\ V \leqslant V_1 \wedge V_2}} \tau(V).$$

3. Let $q$ be any positive rational number. Let $W \in A$ such that $\delta(W) < q/3$. Then by (MM3) there exists $V' \in B$ such that $\delta(V') < q/3$ and $(W, V')$. Let $V = B_{q/3} V' \in B$, one has: $\delta(W) < q/3$, $V' \triangleleft_{q/3} V$, $(W, V')$, hence $W \leqslant \tau(V)$ with $\delta(V) < q$ this proves that

$$W \leqslant \bigvee_{\substack{V \in B \\ \delta(V) < q}} \tau(V)$$

As we have done this for an arbitrary $W$ with $\delta(W) < q/3$ this concludes the proof.

47