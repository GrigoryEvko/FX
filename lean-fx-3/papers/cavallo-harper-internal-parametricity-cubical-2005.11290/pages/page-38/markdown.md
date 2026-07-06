5:38

E. CAVALLO AND R. HARPER

Vol. 17:4

$\triangleright \Psi \Vdash \gamma = \gamma' \in (\Gamma, \xi)$ when $\Psi \Vdash \gamma = \gamma' \in \Gamma$ and $\xi\gamma$ is true.

The open type and term judgments are then defined to hold when their closed instantiations hold.

**Definition 4.11.** We define the open judgments as follows.

$\triangleright \Gamma \gg A = A'$ pretype holds when $\Psi \Vdash A\gamma = A'\gamma'$ pretype for all $\Psi \Vdash \gamma = \gamma' \in \Gamma$.

$\triangleright \Gamma \gg M = M' \in A$ holds when $\Psi \Vdash M\gamma = M'\gamma' \in A\gamma$ for all $\Psi \Vdash \gamma = \gamma' \in \Gamma$.

We note that, in contrast, we define the open *interval* judgments without reference to the terms in the context $\Gamma$. It is therefore not the case that, for example, $v : \perp \gg 0 = 1 \in \mathbb{I}$; interval judgments are prior to term judgments.

**Definition 4.12.** The judgment $\Gamma \gg r \in \mathbb{I}$ is defined to hold when either $r \in \{0, 1\}$ or $(x : \mathbb{I}) \in \Gamma$; an equality $\Gamma \gg r = s \in \mathbb{I}$ is defined to hold when $\Gamma \gg r, s \in \mathbb{I}$ are in the equivalence relation closure of the constraints appearing in $\Gamma$. The judgments $\Gamma \gg r = s \in \mathbf{I}$ and $\Gamma \gg \xi = \xi'$ constraint are defined likewise.

**Definition 4.13.** We define the well-formed contexts inductively.

$\triangleright \cdot = \cdot \text{ctx}$.

$\triangleright (\Gamma, a : A) = (\Gamma', a : A')$ ctx when $\Gamma = \Gamma'$ ctx and $\Gamma \gg A = A'$ pretype.

$\triangleright (\Gamma, x : \mathbb{I}) = (\Gamma', x : \mathbb{I})$ ctx when $\Gamma = \Gamma'$ ctx.

$\triangleright (\Gamma, x : \mathbf{I}) = (\Gamma', x : \mathbf{I})$ ctx when $\Gamma = \Gamma'$ ctx.

$\triangleright (\Gamma, \xi) = (\Gamma', \xi)$ ctx when $\Gamma = \Gamma'$ ctx and $\Gamma \gg \xi = \xi'$ constraint.

A pretype $A$ is a (*Kan*) *type* when it supports the Kan operations, that is, when the operators coe and hcom are well-typed at $A$ and satisfy the necessary equations.

**Definition 4.14** (Kan types). Presupposing $\Psi \Vdash A = A'$ pretype, we say $\Psi \Vdash A = A'$ type when the following conditions hold.

$\triangleright$ For any $(\Psi', x : \mathbb{I}) \Vdash \psi \in \Psi$, if $\Psi' \Vdash r, s \in \mathbb{I}$ and $\Psi' \Vdash M = M' \in A\psi[r/x]$, then

- $\Psi' \Vdash \text{coe}_{x.A\psi}^{r \rightsquigarrow s}(M) = \text{coe}_{x.A'\psi}^{r \rightsquigarrow s}(M') \in A\psi[s/x]$,

- $\Psi' \Vdash \text{coe}_{x.A\psi}^{r \rightsquigarrow r}(M) = M \in A\psi[r/x]$,

$\triangleright$ For any $\Psi' \Vdash \psi \in \Psi$, if $\Psi' \Vdash r, s \in \mathbb{I}, n \in \mathbb{N}$, $\Psi' \Vdash \xi_i$ constraint for all $i < n$, and

- $\Psi' \Vdash M = M' \in A\psi$

- $\Psi', x : \mathbb{I} \Vdash N_i = N'_j \in A\psi$ for all $i, j < n$,

- $\Psi' \Vdash M = N_i[r/x] \in A\psi$ for all $i < n$,

then

- $\Psi' \Vdash \text{hcom}_{A\psi}^{r \rightsquigarrow s}(M; \overrightarrow{\xi_i \hookrightarrow x.N'_i}) = \text{hcom}_{A'\psi}^{r \rightsquigarrow s}(M'; \overrightarrow{\xi_i \hookrightarrow x.N'_i}) \in A\psi$,

- $\Psi' \Vdash \text{hcom}_{A\psi}^{r \rightsquigarrow s}(M; \overrightarrow{\xi_i \hookrightarrow x.N'_i}) = N_i[s/x] \in A\psi$ if $\xi_i$ is true,

- $\Psi' \Vdash \text{hcom}_{A\psi}^{r \rightsquigarrow r}(M; \overrightarrow{\xi_i \hookrightarrow x.N'_i}) = M \in A\psi$.

The extension of the type judgment to open terms is defined as for the pretype judgment: $\Gamma \gg A = A'$ type holds when $\Psi \Vdash A\gamma = A'\gamma'$ type for all $\Psi \Vdash \gamma = \gamma' \in \Gamma$.

We may also define the open substitution judgment following the pattern of the instantiation judgment.

**Definition 4.15.** We define the substitutions $\Gamma \gg \gamma = \gamma' \in \Gamma$ inductively as follows.

$\triangleright \Gamma \gg \cdot = \cdot \in \cdot$.

$\triangleright \Gamma \gg (\gamma, M/a) = (\gamma', M'/a) \in (\Gamma, a : A)$ when $\Gamma \gg \gamma = \gamma' \in \Gamma$ and $\Gamma \gg M = M' \in A\gamma$.