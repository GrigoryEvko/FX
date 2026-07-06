1.2. GRAY OPERATIONS

**Theorem 1.2.1.7** (Steiner). *The functors $\lambda$ and $\nu$ form an adjoint pair*

$$\lambda : \omega\text{-cat} \xrightleftharpoons[\perp]{\text{ADC}} : \nu$$

*For a $\omega$-category $C$, the unit of the adjunction is given by:*

$$\begin{aligned} \eta : & C \rightarrow \nu\lambda C \\ & x \in C_n \mapsto \begin{pmatrix} [d_0^-(x)]_0 & \dots & [d_{n-1}^-(x)]_{n-1} & [x]_n \\ [d_0^+(x)]_0 & \dots & [d_{n-1}^+(x)]_{n-1} & [x]_n \end{pmatrix} \end{aligned}$$

*For an augmented directed complex $K$, the counit is given by:*

$$\begin{aligned} \pi : & \lambda\nu K \rightarrow K \\ & [x]_n \in (\lambda\nu K)_n \mapsto x_n^+ = x_n^- \end{aligned}$$

*Proof.* This is [Ste04, theorem 2.11].

**1.2.1.8.** A *basis* for an augmented directed complex $(K, K^*, e)$ is a graded set $B = (B_n)_{n \in \mathbb{N}}$ such that for every $n$, $B_n$ is both a basis for the monoid $K_n^*$ and for the group $K_n$.

**Remark 1.2.1.9.** The elements of $B_n$ can be characterized as the minimal elements of $K_n^* \setminus 0$ for the following order relation:

$$x \leq y \text{ iff } y - x \in K_n^*$$

This shows that if a basis exists, it is unique.

**1.2.1.10.** Any element of $K_n$ can then be written uniquely as a sum $\sum_{b \in B_n} \lambda_b b$. This leads us to define new operations: For an element $x := \sum_{b \in B_n} \lambda_b b$ of $K_n$, we define the *positive part* and the *negative part*:

$$\begin{aligned} (x)_+ & := \sum_{b \in B_n, \lambda_b > 0} \lambda_b b \\ (x)_- & := \sum_{b \in B_n, \lambda_b < 0} -\lambda_b b \end{aligned}$$

We then have $x = (x)_+ - (x)_-$. An element $x$ is *positive* (resp. *negative*) when $x = (x)_+$ (resp. when $x = -(x)_-$). Let $y = \sum_{b \in B_n} \mu_b b$, we set :

$$x \wedge y := \sum_{b \in B_n} \min(\lambda_b, \mu_b) \ b$$

Eventually, we set

$$\begin{aligned} \partial_n^+(\_) & := (\partial_n(\_))_+ : K_{n+1} \rightarrow K_n^* \\ \partial_n^-(\_) & := (\partial_n(\_))_- : K_{n+1} \rightarrow K_n^* \end{aligned}$$

When an element $b$ of the basis is in the support of $x$, i.e $\lambda_b \neq 0$, we say that $b$ *belongs to $x$*, which is denoted by $b \in x$.

43