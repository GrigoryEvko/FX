CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

**Theorem 4.2.2.9.** *Let $f : C \to D$ be a discrete Conduché functor. The pullback functor $f^* : (\infty, \omega)\text{-cat}_{/D} \to (\infty, \omega)\text{-cat}_{/C}$ preserves colimits.*

In the third section, we study Gray operations for $(\infty, \omega)$-categories. We conclude this chapter by proving results of strictification. In particular, we demonstrate the following theorem:

**Theorem 4.3.3.19.** *Let $C$ be an $(\infty, \omega)$-category, $b$ a globular sum, and $f : b \to C$ any morphism. The $(\infty, \omega)$-categories*

$$1 \stackrel{co}{\star} b \coprod_b C, \; C \coprod_b b \otimes [1] \text{ and } C \coprod_b b \star 1$$

*are strict whenever $C$ is.*

We will also prove the following theorem:

**Theorem 4.3.3.26.** *If $C$ is strict, so are $C \star 1$, $1 \stackrel{co}{\star} C$ and $C \otimes [1]$.*

In the process, we will demonstrate another fundamental equation combining $C \otimes [1]$, $1 \stackrel{co}{\star} C$, $C \star 1$, and $[C, 1]$.

**Theorem 4.3.3.25.** *Let $C$ be an $(\infty, \omega)$-category. The five squares appearing in the following canonical diagram are both cartesian and cocartesian:*

$$\begin{array}{ccc} & C \otimes \{0\} & \longrightarrow & 1 \\ & \downarrow & & \downarrow \\ C \otimes \{1\} & \longrightarrow & C \otimes [1] & \longrightarrow & C \star 1 \\ \downarrow & & \downarrow & & \downarrow \\ 1 & \longrightarrow & 1 \stackrel{co}{\star} C & \longrightarrow & [C, 1] \end{array}$$

*where $[C, 1]$ is the suspension of $C$.*

**About the use of the language of $(\infty, 1)$-categories.** In this chapter and the two following, we will freely use the language of $(\infty, 1)$-categories$^1$.

$^1$As there are currently several directions for the formalization of the language of $(\infty, 1)$-categories ([RV22], [RS17], [Nor19], [CNW]), talking about "the" language of (infinite, 1)-categories may be confusing.

In such case, the reader may consider that we are working within the quasi-category Qcat of **T**-small quasi-categories for **T** a Grothendieck universe. This quasi-category may be obtained either using the coherent nerve as described in [Lur09a, chapter 3], or by considering it as the codomain of the universal co-

174