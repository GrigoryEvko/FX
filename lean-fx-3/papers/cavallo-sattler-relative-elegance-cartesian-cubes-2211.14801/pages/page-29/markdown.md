Relative Elegance and Cartesian Cubes with One Connection

29

### 4.2.2 Unbiased fibrations

In order to apply Corollary 3.33, we must check that we have a fibration between fibrant objects in $\mathrm{PSh}(\square_{\nu})$ classifying fibrations in $\mathrm{PSh}_{\varepsilon}(\square_{\nu})$. This follows from work on cubical models of type theory, specifically the interpretation of universes. Our cube category falls within the ambit of [ABCHFL21], which describes a universe $p_{\mathrm{fib}}: \widehat{U}_{\mathrm{fib}} \to U_{\mathrm{fib}}$ with fibration structures on $p_{\mathrm{fib}}$ and $U_{\mathrm{fib}}$ in type-theoretic terms; Awodey gives a construction of the same in categorical language [Awo23, §§6–8].

However, the fibrations used in these models are not a priori the fibrations we defined in the previous section: they are what Awodey [Awo23] calls unbiased fibrations, which lift not only against (pushout products with) endpoint inclusions $\delta_k: 1 \to \mathbb{I}$ but against generalized points on the interval. To see that $\overline{\square}_{\nu}^{\mathrm{N}}$ is compatible with this model of type theory, we check here that biased (i.e., ordinary) and unbiased fibrations coincide in the presence of a connection.

Definition 4.20 Given $r: B \to \mathbb{I}$ and $f: A \to B$, their unbiased mapping cylinder is the following pushout:

$$\begin{array}{c} A \xrightarrow{f} B \\ \langle r f, \mathrm{id}_A \rangle \Biggl\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbb{I} \times A \xrightarrow[d_r]{} \mathrm{M}_r(f). \end{array}$$

Note that $\mathrm{M}_{\delta_k!_B}(f)$ is the ordinary $k$-sided mapping cylinder (Definition 3.14). We write $r \widehat{\times}_B m: \mathrm{M}_r(m) \to \mathbb{I} \times B$ for the unique map fitting in the diagram

$$\begin{array}{c} A \xrightarrow{f} B \\ \langle r f, \mathrm{id}_A \rangle \Biggl\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbb{I} \times A \xrightarrow[d_r]{} \mathrm{M}_r(f) \\ \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbb{I} \times m \end{array}$$

This is the pushout product in the slice over $B$ of $\langle r, \mathrm{id}_B \rangle: \mathrm{id}_B \to \varepsilon \times B$ and $m: m \to \mathrm{id}_B$, hence the notation. Note that $(\delta_k!_B) \widehat{\times}_B f$ is the ordinary pushout product $\delta_k \widehat{\times} f$.

Definition 4.21 We say $f: Y \to X$ is an unbiased fibration when it has the right lifting property against $r \widehat{\times}_B m$ for all $r: B \to \mathbb{I}$ and $m: A \mapsto B$.

Lemma 4.22 $r \widehat{\times}_B m$ is a trivial cofibration for any $r: B \to \mathbb{I}$ and $m: A \mapsto B$.

2025/10/16 00:43