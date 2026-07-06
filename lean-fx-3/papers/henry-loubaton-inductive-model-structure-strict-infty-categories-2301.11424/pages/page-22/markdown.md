In order to check that the map $i$ is compatible with these sub-polygraphs, it is enough to check that $i(e_n^+)$ is in the domain of $j_+ \hat{\odot} i_n$. To see this, we compute:

$$i(e_n^+) = \pi^+ i(e_{n+1}) = \pi^+(a \otimes e_n) = (a \otimes e_{n-1}^-)\#_{n-1} \dots \#_1 (a \otimes e_0^-)\#_0 (a_0^+ \otimes e_n)$$

and we observe that this expression involves neither $a_0^- \otimes e_n$ nor $a \otimes e_n$, hence it does belong to the domain of $j_+ \hat{\odot} i_n$.

In order to check that the map $p$ is compatible with these sub-polygraphs, we need to check the image by $p$ of all the generators of $I \ominus \mathbb{D}_n^\times$ except $a_0^- \otimes e_n$ and $a \otimes e_n$. These are given by the formulas $p(a_0^e \otimes e_k^p) = e_k^p$ if $k < n$, $p(a_0^+ \otimes e_n) = e_n^+$ and $p(a \otimes e_k^e) = \mathbb{I}_{e_k^e}$, which all indeed belong to the image of $i_n^+$.

### 3 Equations and Saturations in an $m$-Marked $\infty$-Category.

The general goal of this section is to arrive at a better description of the fibrant objects and fibrations between fibrant objects of the model structure of Theorem 2.43. This is achieved using the notion of *equations* in an $\infty$-category introduced by the second named author in [32]. We will recall the basic theory of equations, in a slightly different language, and introduce an analog of equations to deal with the markings, which we call *saturations*.

#### 3.1 Definitions of Equations and Saturations

**3.1 Definition.** A morphism of $m$-marked polygraphs $\Lambda P \rightarrow P$ is a *left equation* if there exists an integer $n$, and two generators $x, y$ of $P$ of dimension respectively $n$ and $n+1$, such that

1. $\Lambda P$ is the $m$-marked sub-polygraph of $P$ that contains all generators except $x$ and $y$,
2. $y$ is a marked arrow,
3. if $n \leq m$, $x$ is an unmarked arrow of $P$,
4. the source of $y$ admits a decomposition:

$$\pi_n^- y = l_n \#_{n-1} (l_{n-1} \#_{n-2} \dots \#_1 (l_1 \#_0 x \#_0 r_1) \#_1 \dots \#_{n-2} r_{n-1}) \#_{n-1} r_n$$

where for each $i$, $l_i$ and $r_i$ are marked $i$-arrows in $P$, with $l_n$ and $r_n$ not containing $x$. In particular, $x$ appears only once in $\pi_n^- y$,

1. $x$ does not appear in the target of $y$.

*Right equations* are defined in the exact same way except the source and target of $y$ are exchanged in the last two conditions.

We say that $\Lambda P \rightarrow P$ is an *equation* to mean that it is either a left or right equation.

**3.2 Remark.** Note that the integer $n$ and the arrows $x$ and $y$ in the previous definition are uniquely determined by the inclusion $\Lambda P \rightarrow P$.

22