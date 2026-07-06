Vol. 22:2

AUTOMATING BOUNDARY FILLING IN CUBICAL TYPE THEORIES

28:13

to mean that they represent equal elements of $G$. Before beginning the reduction, we first show that we can assume the equations in $R$ are of a more restricted form.

**Definition 3.8.** Say a finite presentation $\langle X|R\rangle$ of a group $G$ is *convenient* when

- $X$ is closed under inverses;
- every equation in $R$ is of the form $abc^{-1} = 1$ for some $a, b, c \in X$.

**Proposition 3.9.** *Let $G$ be a finitely presented group. Then $G$ has a convenient presentation.*

*Proof.* Suppose that $G$ is presented by a finite set of generators $X$ and a finite set of equations $y_{i,0}^{\alpha_{i,0}}, \ldots, y_{i,k_i}^{\alpha_{i,k_i}} = 1$ for $0 \le i < n$, where for each $i$ we have $k_i \in \mathbb{N}$ and then $y_{i,j} \in X$ and $\alpha_{i,j} \in \{-1, 1\}$ for $0 \le j \le k_i$.

For each $0 \le i < n$ and $0 \le j \le k_i + 1$, define $z_{i,j} := y_{i,0}^{\alpha_{i,0}}, \ldots, y_{i,j-1}^{\alpha_{i,k_i}} \in G$. Then $G$ is presented by the set of generators $X \cup \{z_{i,j} \mid 0 \le i < n, 0 \le j \le k_i\}$ and equations

$$\begin{array}{rcl} z_{i,0}z_{i,0} & = & z_{i,0} \quad \text{for } 0 \le i < m \\ z_{i,j}y_{i,j} & = & z_{i,j+1} \quad \text{for } 0 \le i < m \text{ and } 0 \le j \le k_i \text{ with } \alpha_{i,j+1} = 1 \\ z_{i,j+1}y_{i,j} & = & z_{i,j} \quad \text{for } 0 \le i < m \text{ and } 0 \le j \le k_i \text{ with } \alpha_{i,j+1} = -1 \\ z_{i,k_i}z_{i,k_i} & = & z_{i,k_i} \quad \text{for } 0 \le i < m \end{array}$$

Note that the first and last equations encode that $z_{i,0} = 1$ and $z_{i,k_i} = 1$ for $0 \le i < m$ respectively.

We encode a (conveniently) finitely presented group $\langle X|R\rangle$ as a context with a single point $\star$. Each generator is encoded as a 1-cell, namely a path from $\star$ to itself, and each equation as a 2-cell.

**Definition 3.10.** In this section, we use $\partial i \mapsto t$ as a shorthand for the pair of boundary entries $i = \mathbf{0} \mapsto t \mid i = \mathbf{1} \mapsto t$.

**Definition 3.11.** Given a convenient presentation $\langle X|R\rangle$, define the context $\lceil X|R \rceil$ ctx to consist of

- a point $\star : [\ ]$,
- a loop $\hat{a}(i) : [\partial i \mapsto \star]$ for each $a \in X$,
- a square

$$s_{a,b,c}(j, k) : [k = \mathbf{0} \mapsto \hat{a}(j) \mid k = \mathbf{1} \mapsto \hat{c}(j) \mid j = \mathbf{0} \mapsto \star \mid j = \mathbf{1} \mapsto \hat{b}(k)]$$

for each equation $abc^{-1} = 1$ in $R$:

$$j \underset{k}{\overset{\hat{b}(k)}{\longmapsto}} \underset{\star}{\overset{\hat{a}(j)}{\longrightarrow}} \underset{\star}{\overset{\hat{s}_{a,b,c}(j, k)}{\longrightarrow}} \hat{c}(j)$$

Any word on $X$ can then be encoded as a path from $\star$ to $\star$ in the context $\lceil X|R \rceil$ ctx.

**Definition 3.12.** Let $\langle X|R\rangle$ be a convenient presentation of a group, $a \in X$ be a generator, and $\lceil X|R \rceil \mid i \vdash t : [\partial i \mapsto \star]$ be a cell. For $e \in \{\mathbf{0}, \mathbf{1}\}$, define cells

$$\lceil X|R \rceil \mid i \vdash t \triangleright_i^e a : [\partial i \mapsto \star]$$

$$\lceil X|R \rceil \mid i, \ell \vdash t \blacktriangleright_{i,\ell}^e a : [i = \mathbf{0} \mapsto \star \mid i = \mathbf{1} \mapsto \hat{a}(\ell) \mid \ell = \mathbf{0} \mapsto t \mid \ell = \mathbf{1} \mapsto t \triangleright_i^e a]$$