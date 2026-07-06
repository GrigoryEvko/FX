1.2. GRAY OPERATIONS

is cocartesian. Furthermore, the induced square in $(0, \omega)$-cat

$$\begin{array}{ccc} \nu K & \xrightarrow{\nu k^0} & \nu M_1 \\ \nu k^0 \downarrow & & \downarrow \nu l^1 \\ \nu M_0 & \xrightarrow{\nu l^0} & \nu M \end{array}$$

is cocartesian.

*Proof.* This is a combination of theorems 3.1.2 and 3.2.7 of [Lou21].

## 1.2.2 Gray operations on augmented directed complexes

We follow Steiner ([Ste04]) and Ara-Maltsiniotis ([AM20]) for the definitions and first properties of Gray operations on augmented directed complexes.

**1.2.2.1.** Let $(K, K^*, e)$ and $(L, L^*, f)$ be two augmented directed complexes. We define the *Gray tensor product* of $(K, K^*, e)$ and $(L, L^*, f)$ as the augmented directed complex

$$(K, K^*, e) \otimes (L, L^*, f) := (K \otimes L, (K \otimes L)^*, e \otimes f)$$

where

- $K \otimes L$ is the chain complex whose value on $n$ is:

$$(K \otimes L)_n := \oplus_{k+l=n} K_k \otimes L_l$$

and the differential is the unique graded group morphism fulfilling:

$$\partial(x \otimes y) := \partial x \otimes y + (-1)^{|x|} x \otimes \partial y$$

where we set the convention $\partial x := 0$ if $|x| = 0$.

- $(K \otimes L)^*$ is given on all integer $n$ by :

$$(K \otimes L)_n^* := \oplus_{k+l=n} K_k^* \otimes L_l^*.$$

- $e \otimes f : K_0 \otimes L_0 \to \mathbb{Z}$ is the unique morphism fulfilling

$$(e \otimes f)(x \otimes y) = e(x)f(y).$$

**1.2.2.2.** The Gray tensor product induces a monoidal structure on ADC. Its unit is given by $\lambda \mathbf{D}_0$. Furthermore, Steiner shows that if $K$ and $L$ admit loop free and unitary bases, so does $K \otimes L$. The monoidal structure then restricts to a monoidal structure on $\text{ADC}_\text{B}$. Eventually [AM20, proposition A.20] provides an equivalence

$$(K \otimes L)^\circ \cong K^\circ \otimes L^\circ \quad (1.2.2.3)$$

47