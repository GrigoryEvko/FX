2.4. GLOBULAR EQUIVALENCES

**Proposition 2.4.4.2.** *There exists a zigzag of weakly invertible natural transformations*

$$i \rightsquigarrow j$$

where $j$ is a left Quillen functor such that $j([n]) = i([n])$ and $j([n]_t) = \tau_{n-1}^i i([n])$, and such that the image of $[n] \to [n]_t$ by $j$ is induced by the canonical morphism $id \to \tau_{n-1}^i(id)$.

*Proof.* We define $\tilde{i}$ (resp. $j$) to be the colimit preserving functor defined on representables by $\tilde{i}([n]) := i([n])$ and $\tilde{i} := ([n]_t) = \tau_{n-1}^i i([n]_t)$ (resp. $j([n]) := i([n])$ and $j([n]_t) := \tau_{n-1}^i i([n]))$. We then have a zigzag of natural transformations

$$i \xrightarrow{\sim} \tilde{i} \xleftarrow{\sim} j.$$

that are pointwise acyclic cofibrations according to 2.4.4.1. This implies that both $\tilde{i}$ and $j$ are left Quillen functors.

In the following lemmas, we use the Steiner theory recalled in section 1.2.1.

**Lemma 2.4.4.3.** *Let $m$ be an integer and $X$ and $Y$ be two $(0, \omega)$-categories admitting a loop free and atomic basis. We denote by $0$, $1$ and $t$ the three points of $\Sigma X \vee [1]$. Let*

$$f : \Sigma^m([X, 1] \star Y) \to \Sigma^m(([X, 1] \vee [1]) \star Y)$$

*be a morphism fitting in the following diagram:*

$$\begin{array}{ccc} \Sigma^m((\{0\} \coprod \{1\}) \star Y) & \xrightarrow{\Sigma^m(g \star Y)} & \Sigma^m(([X, 1] \vee [1]) \star Y) \\ \downarrow & \xrightarrow{f} & \downarrow \\ \Sigma^m([X, 1] \star Y) & \xrightarrow{id} & \Sigma^m([X, 1] \star Y) \end{array}$$

where $g$ sends $0$ on $0$, and sends $1$ on $t$ and the right vertical morphism induced by the retraction $[X, 1] \vee [1] \to [X, 1]$.

Then $f$ is $\Sigma^m(\nabla \star Y)$.

*Proof.* All these categories admit loop free and atomic basis. We can then show this lemma in the category of augmented directed complexes. Furthermore, in this category, the suspension only makes an index shift, so we can assume without loss of generality that $m = 0$.

The commutativity of the diagram implies that

$$\begin{array}{rcl} f(0 \star x) & = & 0 \star x \\ f(1 \star x) & = & t \star x \\ f([x, 1] \star y) & = & [x, 1] \star y + r_{x,y} \end{array}$$

where $r_{x,y}$ is a positive sum of elements of $(B_{[1]\star Y})_{|x|+|y|+1}$. We show by induction on $|x| + |y|$ that:

$$\begin{array}{rcl} r_{x,y} & = & [1] \star y \quad \text{if } |x| = 0 \\ & = & 0 \quad \text{if } |x| > 0. \end{array}$$

93