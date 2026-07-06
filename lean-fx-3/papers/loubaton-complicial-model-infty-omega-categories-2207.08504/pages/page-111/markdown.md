3.1. PRELIMINARIES

by setting $[1]_t \otimes [a, m]$ as the colimit

$$\begin{array}{c} \coprod_{l \leq m} \operatorname{colim}_{[k_0, k_1] \to [1] \otimes \{l\}} [[k_0] \otimes a, k_1] \longrightarrow \operatorname{colim}_{[k_0, k_1] \to [1] \otimes [m]} [[k_0]^\sharp \otimes a, k_1] \\ \downarrow \hspace{2em} \scriptstyle{r} \quad \downarrow \\ \coprod_{l \leq m} \operatorname{colim}_{[k_0, k_1] \to [1] \otimes \{l\}} \tau_0^i[e, k_1] \longrightarrow [1]_t \otimes [a, m] \end{array}$$

and for any integer $k > 1$,

$$[k]_t \otimes [a, n] := [k] \otimes [a, n],$$

and eventually, for any stratified simplicial set $K$, by setting $K \otimes [e, 1]_t$ as the pushout

$$\begin{array}{c} \coprod_{c \in ob(K)} \tau_1^i(\{c\} \otimes [e, 1]) \longrightarrow \tau_1^i(K \otimes [e, 1]) \\ \downarrow \hspace{2em} \scriptstyle{r} \quad \downarrow \\ \coprod_{c \in ob(K)} \{c\} \otimes [e, 1]_t \longrightarrow K \otimes [e, 1]_t \end{array}$$

**Notation 3.1.4.5.** We will denote by $K_1 \otimes \ldots \otimes K_n \otimes C$ the object $(K_1 \otimes (\ldots \otimes (K_n \otimes C) \ldots))$

**Proposition 3.1.4.6.** *The functor $\otimes : \mathrm{tPsh}(\Delta)^1 \times \mathrm{tSeg}(A) \to \mathrm{tSeg}(A)$ is a left Quillen functor.*

*Proof.* We first fix an object $[a, n]$ in $\operatorname{Seg}(A)$. The functor $\_ \otimes [a, \_] : \operatorname{Psh}(\Delta) \times \operatorname{Psh}(\Delta) \to \operatorname{Seg}(A)$ is the composite

$$\operatorname{Psh}(\Delta) \times \operatorname{Psh}(\Delta) \xrightarrow{\otimes} \operatorname{Psh}(\Theta_2) \xrightarrow{i^*} \operatorname{Psh}(\Delta[\Delta]) \cong \operatorname{Seg}(\operatorname{Psh}(\Delta)) \xrightarrow{\operatorname{Seg}(\_ \otimes a)} \operatorname{Seg}(A)$$

According to propositions 2.1.1.8 and 1.1.3.17 and theorem 1.2.5.3, this functor then sends $W_1 \times W_1$ to weak equivalence of $\operatorname{Seg}(A)$. We can show similarly that $\_ \otimes [e, 1]_t : \operatorname{Psh}(\Delta) \to \mathrm{tSeg}(A)$ and $[1]_t \otimes [a, \_] : \operatorname{Psh}(\Delta) \to \mathrm{tSeg}(A)$ sends $W_1$ to weak equivalences of $\operatorname{Seg}(A)$.

We now fix a marked simplicial set $K$ and an integer $n$. Let $i : a \to b$ be a weak equivalence of $A$. The morphism $K \otimes [a, n] \to K \otimes [b, n]$ is a colimit of natural transformations that is pointwise a weak equivalence. As this colimit is indexed by the elegant Reedy category $\Theta_{/K \otimes [n]}$ and verifies the condition of theorem 2.1.1.7, the morphism $K \otimes [i, n] : K \otimes [a, n] \to K \otimes [b, n]$ is a weak equivalence.