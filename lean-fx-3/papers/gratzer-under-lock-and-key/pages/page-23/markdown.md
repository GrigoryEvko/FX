$$\operatorname{let}_{\rho} \operatorname{mod}_{\xi}(x_{A}) \leftarrow M \text { in } N[\Gamma ; \alpha ; \Delta] \stackrel{\text { def }}{=} \operatorname{let}_{\rho} \operatorname{mod}_{\xi}(x_{A}) \leftarrow M[\Gamma ; \alpha ; \Delta, \widehat{\mathbf{0}}_{\rho}] \text { in } N[\Gamma ; \alpha ; \Delta, x:(\rho \circ \xi \mid A)]$$

$$(M, N)[\Gamma ; \alpha ; \Delta] \stackrel{\text { def }}{=} (M[\Gamma ; \alpha ; \Delta], N[\Gamma ; \alpha ; \Delta])$$

$$\pi_{i}(M)[\Gamma ; \alpha ; \Delta] \stackrel{\text { def }}{=} \pi_{i}(M[\Gamma ; \alpha ; \Delta])$$

$$\operatorname{in}_{i}(M)[\Gamma ; \alpha ; \Delta] \stackrel{\text { def }}{=} \operatorname{in}_{i}(M[\Gamma ; \alpha ; \Delta])$$

$$\operatorname{case}(M ; x_{A} . P ; y_{B} . Q)[\Gamma ; \alpha ; \Delta] \stackrel{\text { def }}{=} \operatorname{case}(M[\Gamma ; \alpha ; \Delta]; x_{A} . P[\Gamma ; \alpha ; \Delta, x:(1 \mid A)] ; y_{B} . Q[\Gamma ; \alpha ; \Delta, y:(1 \mid B)])$$

**Theorem 5.2** (Lock Weakening). *In the following rule the term in the conclusion is well-defined when the premises hold, and the rule itself is admissible.*

$$\frac{\Gamma, \widehat{\mathbf{0}}_{\mu}, \Delta \vdash M : A @ p \quad \alpha : \mu \Rightarrow \nu}{\Gamma, \widehat{\mathbf{0}}_{\nu}, \Delta \vdash M[\Gamma ; \alpha ; \Delta] : A @ p}$$

*Proof.* By induction on the derivation of $\Gamma, \widehat{\mathbf{0}}_{\mu}, \Delta \vdash M : A @ p$. We prove only the non-trivial cases: the rest follow by straightforward applications of the IH.

$$\operatorname{CASE}(\Gamma, x:(\rho \mid A), \Gamma', \widehat{\mathbf{0}}_{\mu}, \Delta \vdash x^{\alpha'} : A @ a).$$

We have that

$$x^{\alpha'}[\Gamma, x:(\rho \mid A), \Gamma'; \alpha ; \Delta] \stackrel{\text { def }}{=} x^{\operatorname{locks}(\Gamma') * \alpha * 1_{\operatorname{locks}(\Delta)} \circ \alpha'}$$

The result then follows, for $\alpha': \rho \Rightarrow \operatorname{locks}(\Gamma') \circ \mu \circ \operatorname{locks}(\Delta)$, whence

$$\operatorname{locks}(\Gamma') * \alpha * 1_{\operatorname{locks}(\Delta)} \circ \alpha': \rho \Rightarrow \operatorname{locks}(\Gamma') \circ \nu \circ \operatorname{locks}(\Delta)$$

$$\operatorname{CASE}(\Gamma, \widehat{\mathbf{0}}_{\mu}, \Delta, x:(\rho \mid A), \Delta' \vdash x^{\alpha'} : A @ a).$$

The result immediately follows because $x^{\alpha'}[\Gamma ; \alpha ; \Delta, x:(\rho \mid A), \Delta'] \stackrel{\text { def }}{=} x^{\alpha'}$.

$$\operatorname{CASE}(\Gamma, \widehat{\mathbf{0}}_{\mu}, \Delta \vdash \operatorname{mod}_{\xi}(M):\langle \xi \mid A \rangle @ p).$$

Writing $\xi: a \rightarrow p$, it must be that

$$\Gamma, \widehat{\mathbf{0}}_{\mu}, \Delta, \widehat{\mathbf{0}}_{\xi} \vdash M : A @ a$$

By the IH, we get that

$$\Gamma, \widehat{\mathbf{0}}_{\nu}, \Delta, \widehat{\mathbf{0}}_{\xi} \vdash M[\Gamma ; \alpha ; \Delta, \widehat{\mathbf{0}}_{\xi}] : A @ a$$

so by an application of MOD we have

$$\Gamma, \widehat{\mathbf{0}}_{\nu}, \Delta \vdash \operatorname{mod}_{\xi}(M[\Gamma ; \alpha ; \Delta, \widehat{\mathbf{0}}_{\xi}]):\langle \xi \mid A \rangle @ a$$

But as this is exactly $\operatorname{mod}_{\xi}(M)[\Gamma ; \alpha ; \Delta]$ we obtain the result.

23