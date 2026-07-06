2.4. GLOBULAR EQUIVALENCES

## 2.4 Globular equivalences

### 2.4.1 Homotopy categories

2.4.1.1. The $n$-globe is the marked simplicial set $\mathbf{D}_n := \Sigma^n[0]$. We then have $\mathbf{D}_0 := [0]$ and $\mathbf{D}_{n+1} := \Sigma\mathbf{D}_n$. This defines a globular object in $\mathrm{mPsh}(\Delta)$:

$$\mathbf{D}_0 \xrightarrow[i_0^-]{i_0^+} \mathbf{D}_1 \xrightarrow[i_1^-]{i_1^+} \mathbf{D}_2 \xrightarrow[i_3^-]{i_3^+} \dots$$

and we have equalities:

$$i_{n+1}^- i_n^+ = i_{n+1}^+ i_n^- \quad i_{n+1}^+ i_n^- = i_{n+1}^+ i_n^+.$$

We also set $(\mathbf{D}_n)_t := \tau_{n-1}^i(\mathbf{D}_n)$ for $n > 0$ and $\partial\mathbf{D}_n := \Sigma^n\emptyset$. We then have a canonical inclusions

$$\partial\mathbf{D}_0 \to \mathbf{D}_0$$

and for any $n > 0$, we have canonical inclusions

$$\partial\mathbf{D}_n \to \mathbf{D}_n \to (\mathbf{D}_n)_t.$$

Let $C$ be a complicial set. A $n$-cell $a$ of $C$ is a morphism $a : \mathbf{D}_n \to C$. If $n$ is non null, the *source* of $a$ (resp. the *target* of $a$) is the $(n-1)$-cell $a \circ i_{n-1}^-$ (resp. $a \circ i_{n-1}^+$). The cell $a$ is thin if the corresponding morphism $\mathbf{D}_n \to C$ factorizes via $(\mathbf{D}_n)_t$.

2.4.1.2. From now on, and until the end of this section, we fix a complicial set $C$. All considered cells are cells of $C$.

Let $n$ be a non null integer, and $a, b$ two $n$-cells. Cells $a$ and $b$ are *parallel* if they share the same source and the same target. They are *composable* if the source of $a$ is the target of $b$.

Let $a$ and $b$ be two parallel cells. The cell $a$ is *equivalent* to the cell $b$ if there exists a thin $(n+1)$-cell $d : a \to b$, or equivalently, if there exists a homotopy $\mathbf{D}_n \times [1]_t$ between $a$ and $b$, and constant on $\partial\mathbf{D}_n \times [1]_t$. This relation is denoted by $\sim$.

**Lemma 2.4.1.3.** *The relation $\sim$ is reflexive, symmetric and transitive.*

*Proof.* This comes from usual properties of fibrant objects.

**Lemma 2.4.1.4.** *Let $a, b$ be two equivalent cells. If $a$ is thin, so is $b$.*

*Proof.* As $\{0\} \to [1]_t$ is a weak equivalence, so is $\mathbf{D}_n \times [1]_t \cup (\mathbf{D}_n)_t \times \{0\} \to (\mathbf{D}_n)_t \times [1]_t$. As $C$ is fibrant, this directly implies the result.

93