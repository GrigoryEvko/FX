CHAPTER 2. STUDY OF COMPLICIAL SETS

For the second assertion, remark that $[1]_t \star [0]$ is $\tau_1^i([1]_t \star \emptyset \cup [1] \star [0])$. As $\tau_1^i$ is a left Quillen functor, the theorem 2.3.2.1 induces a zigzag of acyclic cofibration between $[1]_t \star \emptyset \cup [1] \star [0] \to [1]_t \star [0]$ and

$$[1]_t \forall [1] \coprod_{[1]} \Sigma[1] \to [1]_t \forall [1] \coprod_{[1]} \Sigma[1]_t.$$

As this cofibration is a pushout of $\Sigma[1] \to \Sigma[1]_t$, this concludes the proof.

Corollary 2.3.2.3. Let $f : C \to D$ be a fibration between complicial sets, and $K \to L$ a cofibration. If $f$ has the right lifting property against

$$\Sigma(L \star \emptyset \cup K \star [0]) \to \Sigma(L \star [0]),$$

then $f$ has the right lifting property against

$$[0] \stackrel{co}{\star} \Sigma K \cup \emptyset \star \Sigma L \to [0] \stackrel{co}{\star} \Sigma L.$$

If $f$ has the right lifting property against $\Sigma[1] \to \Sigma[1]_t$, then $f$ has the right lifting property against

$$[0] \stackrel{co}{\star} [1] \cup \emptyset \star [1]_t \to [0] \stackrel{co}{\star} [1]_t$$

Proof. The proof is similar to the one of corollary 2.3.2.2.

## 2.4 Globular equivalences

### 2.4.1 Homotopy categories

Definition 2.4.1.1. The $n$-globe is the marked simplicial set $\mathbf{D}_n := \Sigma^n[0]$. We then have $\mathbf{D}_0 := [0]$ and $\mathbf{D}_{n+1} := \Sigma \mathbf{D}_n$. This defines a globular object in $\mathrm{mPsh}(\Delta)$:

$$\mathbf{D}_0 \xrightarrow[i_0]{i_0^+} \mathbf{D}_1 \xrightarrow[i_1]{i_1^+} \mathbf{D}_2 \xrightarrow[i_2]{i_2^+} \dots$$

and we have equalities:

$$i_{n+1}^- i_n^+ = i_{n+1}^+ i_n^- \quad i_{n+1}^+ i_n^- = i_{n+1}^+ i_n^+.$$

We also set $(\mathbf{D}_n)_t := \tau_{n-1}^i(\mathbf{D}_n)$ for $n > 0$ and $\partial \mathbf{D}_n := \Sigma^n \emptyset$. We then have a canonical inclusions

$$\partial \mathbf{D}_0 \to \mathbf{D}_0$$

and for any $n > 0$, we have canonical inclusions

$$\partial \mathbf{D}_n \to \mathbf{D}_n \to (\mathbf{D}_n)_t.$$

Let $C$ be a complicial set. A $n$-cell $a$ of $C$ is a morphism $a : \mathbf{D}_n \to C$. If $n$ is non null, the source of $a$ (resp. the target of $a$) is the $(n-1)$-cell $a \circ i_{n-1}^-$ (resp. $a \circ i_{n-1}^+$). The cell $a$ is marked if the corresponding morphism $\mathbf{D}_n \to C$ factorizes via $(\mathbf{D}_n)_t$.

84