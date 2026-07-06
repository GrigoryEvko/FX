Iterated smash products

273

**Definition 15.4.3 (Identity and composites of pointed functions).** Given $A_*: \mathrm{U}_*$ in any mode $m$, we define the pointed identity function $\mathrm{id}_*(A_*) \in A_* \to A_* @ m$ as follows.

$$\mathrm{id}_*(A_*) := \langle \lambda a. a, \lambda^\top \dots a_0 \rangle$$

Given two pointed functions $f: A_* \to B_*$ and $g: B_* \to C_*$, we define their pointed composite $g_* \circ_* f_* \in A_* \to C_* @ m$ as follows

$$g_* \circ_* f_* := \langle \lambda a. g(f a), \lambda^\top x. \mathrm{hcom}_C^{0 \to 1}(g(f_0 x); x \equiv 0 \hookrightarrow \dots g(f a_0), x \equiv 1 \hookrightarrow y. g_0 y) \rangle$$

The second component here is the composite of the path $\lambda^\top x. g(f_0 x)$ from $g(f a_0)$ to $g b_0$ with the path $g_0$ from $g b_0$ to $c_0$.

We take a few basic algebraic properties of pointed functions for granted, namely the unit laws and associativity of pointed composition.

The first essential result for constructing shadows is the following isomorphism, which equates pointwise functions with globally-defined parametric functions between discrete types.

**Lemma 15.4.4.** Given a pair of pointed types $A_*, B_*: \mathrm{U}_*$ and $f_*: A_* \to B_*$, we have a term $\diamond_* f_* \in \mathrm{Glo}(\mathrm{Disc}_*(A_*) \to \mathrm{Disc}_*(B_*)) @ \mathrm{pt}$. Conversely, given a global pointed function $u: \mathrm{Glo}(\mathrm{Disc}_*(A_*) \to \mathrm{Disc}_*(B_*))$, we have a term $\blacklozenge_* u \in A_* \to B_* @ \mathrm{pt}$. The two functions $\diamond_*$ and $\blacklozenge_*$ constitute an isomorphism.

*Proof.* We define $\diamond_* f_*$ and $\blacklozenge_* u$ as follows.

$$\diamond_* f_* := \mathrm{mod}(\langle \mathrm{map-disc} f, \lambda^\top x. \mathrm{mod}(f_0 x) \rangle)$$

$$\blacklozenge_* u := \langle \lambda a. \mathrm{undisc}(\mathrm{fst}(\mathrm{unmod}(u)) (\mathrm{mod}(a))), \lambda^\top x. \mathrm{undisc}(\mathrm{snd}(\mathrm{unmod}(u)) x) \rangle$$

One inverse condition holds up to exact equality: we have $\blacklozenge_* \diamond_* f_* = f_* \in A_* \to B_*$ for any $f_*: A_* \to B_*$. For the other, given any $u: \mathrm{Glo}(\mathrm{Disc}_*(A_*) \to \mathrm{Disc}_*(B_*))$, we have a path $\diamond_* \blacklozenge_* u \rightsquigarrow u$ defined as follows. First we construct an auxiliary family of paths as follows.

$$H \in \mathrm{Glo}((d: \mathrm{Disc}(A)) \to \mathrm{Path}(\mathrm{Disc}(B), \mathrm{fst}(\mathrm{unmod}(\diamond_* \blacklozenge_* u)) d, \mathrm{fst}(\mathrm{unmod}(u)) d))$$

$$H := \mathrm{mod}\left( \lambda d. \left[ \begin{array}{l} \text{case } d \text{ of} \\ | \mathrm{mod}(a) \mapsto \mathrm{unmod}(\mathrm{undisc-uniq}(\mathrm{unmod}(u) (\mathrm{mod}(a)))) \end{array} \right] \right)$$

Then we use this to define a path $P$ from $\diamond_* \blacklozenge_* u$ to $u$.

$$P := \lambda^\top y. \mathrm{mod}(\langle \lambda d. \mathrm{unmod}(H) d y, \lambda^\top x. \mathrm{undisc-uniq}(f_0 x) y \rangle)$$

□