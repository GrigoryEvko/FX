Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:19

2.3. The extent operator. As we have mentioned, the first reason for using affine variables is connected to function extensionality. If we follow the standard relational model of type theory—more generally, the standard definition of a logical relation at function type—we expect the following isomorphism, a bridge equivalent of Lemmas 1.1 and 1.2.

$$\mathsf{Bridge}_{\boldsymbol{x},(a:A)\to B}(F_0,F_1)$$

$$\simeq$$

$$(a_0:A[\mathbf{0}/\boldsymbol{x}])(a_1:A[\mathbf{1}/\boldsymbol{x}])(p:\mathsf{Bridge}_{\boldsymbol{x},A}(a_0,a_1))\to\mathsf{Bridge}_{\boldsymbol{x},B[p\otimes\boldsymbol{x}/a]}(F_0a_0,F_1a_1)$$

To go from bottom to top, we can repeat the proof of Lemma 1.1 without issue. On the other hand, the proof of Lemma 1.2 relies on the presence of coe, which has no equivalent in parametric type theory. Instead, we will introduce a new operator to validate this principle, extent, which relies on the substructurality of the bridge interval.

Rules for extent are displayed in Figure 5. The operator is essentially a fully applied version of the principle we are looking for.

Lemma 2.1. Let $x:\mathbb{I}\gg A$ type, $x:\mathbb{I},a:A\gg B$ type, $F_0\in((a:A)\to B)[\mathbf{0}/\boldsymbol{x}]$, and $F_1\in((a:A)\to B)[\mathbf{1}/\boldsymbol{x}]$ be given. Then we have the following.

$$\frac{H\in(a_0:A[\mathbf{0}/\boldsymbol{x}])(a_1:A[\mathbf{1}/\boldsymbol{x}])(p:\mathsf{Bridge}_{\boldsymbol{x},A}(a_0,a_1))\to\mathsf{Bridge}_{\boldsymbol{x},B[p\otimes\boldsymbol{x}/a]}(F_0a_0,F_1a_1)}{\mathsf{bridge-funext}(H)\in\mathsf{Bridge}_{\boldsymbol{x},(a:A)\to B}(F_0,F_1)}$$

Proof. $\mathsf{bridge-funext}(H):=\lambda^{\mathbf{I}}\boldsymbol{x}.\lambda a.\mathsf{extent}_{\boldsymbol{x}}(a;a_0.F_0a_0,a_1.F_1a_1,a_0.a_1.\overline{a}.Ha_0a_1\overline{a})$.

As shown in the rule EXTENT-$\beta$, $\mathsf{extent}_{\boldsymbol{r}}$ evaluates by capturing the occurrences of $\boldsymbol{r}$ in its principal argument $M$. That is, $\mathsf{extent}_{\boldsymbol{x}}(M;a_0.F_0a_0,a_1.F_1a_1,a_0.a_1.\overline{a}.Ha_0a_1\overline{a})$ evaluates by passing $M[\mathbf{0}/\boldsymbol{x}]$, $M[\mathbf{1}/\boldsymbol{x}]$, and $\lambda^{\mathbf{I}}\boldsymbol{x}.M$ to $H$. That this is possible depends on affinity because $\lambda^{\mathbf{I}}\boldsymbol{x}.-$ does not necessarily commute with diagonal substitutions. Specifically, if we have some term $M(\boldsymbol{x},\boldsymbol{y})$ that depends on two variables, we can get different results by abstracting before or after substitution as follows.

$$\begin{array}{ccc} M(\boldsymbol{x},\boldsymbol{y}) & \xrightleftharpoons{[\boldsymbol{y}/\boldsymbol{x}]} & M(\boldsymbol{y},\boldsymbol{y}) \\ \lambda^{\mathbf{I}}\boldsymbol{x}.- & & \Downarrow \lambda^{\mathbf{I}}\boldsymbol{x}.- \\ \lambda^{\mathbf{I}}\boldsymbol{x}.M(\boldsymbol{x},\boldsymbol{y}) & \xrightleftharpoons{[\boldsymbol{y}/\boldsymbol{x}]} & \lambda^{\mathbf{I}}\boldsymbol{x}.M(\boldsymbol{x},\boldsymbol{y}) \neq \lambda^{\mathbf{I}}\boldsymbol{x}.M(\boldsymbol{y},\boldsymbol{y}) \end{array}$$

We call the operator extent because $\mathsf{extent}_{\boldsymbol{r}}(M;\cdots)$ reveals the extent of the term $M$ in the direction $\boldsymbol{r}$: either $\boldsymbol{r}$ is a constant, in which case $M$ is simply a point, or $\boldsymbol{r}$ is a variable $\boldsymbol{x}$, in which case $M$ is a point on a line $\lambda^{\mathbf{I}}\boldsymbol{x}.M$ in that direction.

The conditions under which EXTENT-$\beta$ applies are somewhat subtle. In short, the requirement is that $M$ not depend on any term variables that are not apart from $\boldsymbol{x}$. For example, $\mathsf{extent}_{\boldsymbol{x}}(a;\cdots)$ can be reduced only when $a$ appears prior to $\boldsymbol{x}$ in the context. Once again, this relates to the commutativity of substitutions and capture, in this case the difference between $(\lambda^{\mathbf{I}}\boldsymbol{x}.a)[Q(\boldsymbol{x})/a]$ and $\lambda^{\mathbf{I}}\boldsymbol{x}.(a[Q(\boldsymbol{x})/a])$. Note, however, that an extent term containing no term variables always reduces, so this issue is invisible to the closed operational semantics; it is merely a matter of the degree to which we can extend the closed reduction rule to an equality for open terms.

We can show that bridge-funext is in fact an isomorphism, with inverse given by the bridge equivalent of Lemma 1.1. One inverse condition is EXTENT-$\beta$, while the other is an