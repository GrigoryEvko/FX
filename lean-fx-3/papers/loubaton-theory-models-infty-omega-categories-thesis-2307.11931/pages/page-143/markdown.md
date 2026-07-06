3.2. GRAY CONSTRUCTIONS FOR STRATIFIED SEGAL A-CATEGORIES

### 3.2.4 Gray constructions are left Quillen

In this section, we show that the Gray cylinder is a Quillen functor. Combined with the proposition 3.2.3.2, this will imply that the Gray cone is Quillen.

3.2.4.1. Let $x : [k_0] \star [k_1]^{op} \star [k_2] \to [n]$ be an element of $\Delta^3_{/[n]}$. The degree of $x$, is $f(0) - f(k_1)$ where $f$ is the composite morphism:

$$f : [k_1]^{op} \to [k_0] \star [k_1]^{op} \star [k_2] \to [n]$$

We will denote by $K_{\le i}$ the full subcategory of $\Delta^3_{/[n]}$ whose objects are of degree inferior or equal to $i$.

An element $x : [k_0] \star [k_1]^{op} \star [k_2] \to [n]$ of degree $d$ is regular if $k_1 = d$, $k_0 + k_1 + k_2 = n$ and

$$x(l) := \begin{cases} l & \text{if } l \le k_0 \\ l-1 & \text{if } k_0 < l \le k_0 + k_1 \\ l-2 & \text{if } k_0 + k_1 < l \end{cases}$$

Remark that the regular object $x$ is characterized by the triple $(k_0, k_1, k_2)$.

3.2.4.2. Let $x : [k_0] \star [k_1]^{op} \star [k_2] \to [n]$ be an element $\Delta^3_{/[n]}$, and $i : [0] \to [k_0] \star [k_1]^{op} \star [k_2]$ a morphism. We denote by $d^i x := [k'_0] \star [k'_1]^{op} \star [k'_2] \xrightarrow{d} [k_0] \star [k_1]^{op} \star [k_2] \to [n]$ the morphism that avoids $i$, and where $k'_j := k_j - 1$ if $i$ factors through $[k_j]$ and $k'_j := k_j$ if not. We then define $(\Delta^3_{/[n]})_{/\Lambda^i x}$ as the full subcategory of $(\Delta^3_{/[n]})_x$ that includes any non negative object $x' \to x$ that are different of $d^i x \to x$ and $id : x \to x$.

Lemma 3.2.4.3. For any regular object $x : [k_0] \star [k_1]^{op} \star [k_2] \to [n]$ and for any $i : [0] \to [k_0] \star [k_1]^{op} \star [k_2]$ which is neither $k_0 + 1$ nor $k_0 + k_1 + 1$, the morphism

$$\underset{(\Delta^3_{/[n]})_{\Lambda^i x}}{\operatorname{colim}} [a, \_] \vee [\_ \otimes a, 1] \vee [a, \_] \to [a, k_0] \vee [[k_1] \otimes a, 1] \vee [a, k_2]$$

is an acyclic cofibration.

Proof. Suppose first that the image of $i$ is in $[k_0]$. There is a cocartesian square:

$$\begin{array}{c} [[k_1] \otimes a, \Lambda^i [k_0 + 1 + k_2]] \cup [\partial [k_1] \otimes a, [k_0 + 1 + k_2]] \to \underset{(\Delta^3_{/[n]})_{/\Lambda^i x}}{\operatorname{colim}} [a, \_] \vee [\_ \otimes a, 1] \vee [a, \_] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [[k_1] \otimes a, [k_0 + 1 + k_2]] \xrightarrow{} [a, k_0] \vee [[k_1] \otimes a, 1] \vee [a, k_2] \end{array}$$

133