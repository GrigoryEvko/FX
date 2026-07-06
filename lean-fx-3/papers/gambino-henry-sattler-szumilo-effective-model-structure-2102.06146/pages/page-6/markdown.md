**Remark 1.1.** There are two alternative ways of viewing the evaluation functor. First, since $\mathcal{E}$ has finite limits, we can consider $X(K)$ as the value on $K$ of the right Kan extension of $X: \Delta^{\text{op}} \to \mathcal{E}$ along the inclusion of $\Delta$ into the category of finite simplicial sets. Secondly, seeing $\mathcal{E}$ as a Set-enriched category, we can view $X(K)$ as a weighted limit, namely the limit of $X$, viewed as a diagram in $\mathcal{E}$, weighted by $K$, viewed as a diagram in Set. Both of these observations show that $X(K)$ is contravariantly functorial in $K$.

We write $\widehat{\text{ev}}$ for the *pullback evaluation* functor, which is the result of applying the so-called Leibniz construction [RV14] to the two-variable functor $\text{ev}$, i.e., the functor sending a map $i: A \to B$ between finite simplicial sets and a morphism $f: X \to Y$ of $\mathfrak{s}\mathcal{E}$ to

$$\widehat{\text{ev}}_i(f): \text{ev}_A(X) \to \text{ev}_B(X) \times_{\text{ev}_B(Y)} \text{ev}_A(Y) \text{ in } \mathcal{E} \\ \text{also written as } \widehat{\text{ev}}_i(f): X(A) \to X(B) \times_{Y(B)} Y(A). \tag{1.5}$$

**Remark 1.2.** We adopt the convention of prefixing with 'pullback' (or 'pushout') the name of a two-variable functor to indicate the result of applying the Leibniz construction to it. So for example, we shall say pushout product for what is also referred to as Leibniz product or corner product.

We use standard notation for the sets of boundary inclusions and horn inclusions,

$$I_{\mathfrak{sSet}} = \{\partial \Delta[n] \to \Delta[n] \mid n \geq 0\} \text{ and } J_{\mathfrak{sSet}} = \{\Lambda^k[n] \to \Delta[n] \mid n \geq k \geq 0, n > 0\}. \tag{1.6}$$

**Definition 1.3.** We say that a morphism in $\mathfrak{s}\mathcal{E}$ is

- a *trivial Kan fibration* if its pullback evaluations with all maps in $I_{\mathfrak{sSet}}$ are split epimorphisms;
- a *Kan fibration* if its pullback evaluations with all maps in $J_{\mathfrak{sSet}}$ are split epimorphisms.

Explicitly, a map $f: X \to Y$ in $\mathfrak{s}\mathcal{E}$ is a Kan fibration if the morphism

$$X(\Delta[n]) \to X(\Lambda^k[n]) \times_{Y(\Lambda^k[n])} Y(\Delta[n])$$

in $\mathcal{E}$ has a section, for all $n \geq k \geq 0$ and $n > 0$. For $Y = 1$, this means that the morphism

$$X(\Delta[n]) \to X(\Lambda^k[n])$$

has a section, for all $n \geq k \geq 0$ and $n > 0$, in which case we say that $X$ is a *Kan complex*. Note that for $\mathcal{E} = \text{Set}$, these definitions reduce to the standard notions of a Kan fibration, trivial Kan fibration and a Kan complex in simplicial sets. In the following, we shall frequently write *fibration*, *trivial fibration* and *fibrant object*, as we do not consider other notions of fibrations.

Although we have not yet introduced cofibrations and trivial cofibrations in $\mathfrak{s}\mathcal{E}$, we can use the standard classes of cofibrations and trivial cofibrations in $\mathfrak{sSet}$, which are the saturations of the generating sets $I_{\mathfrak{sSet}}$ and $J_{\mathfrak{sSet}}$, respectively.

The next proposition characterises fibrations and trivial fibrations by reducing them to the corresponding notions in $\mathfrak{sSet}$ in terms of the $\mathfrak{sSet}$-enrichment of $\mathfrak{s}\mathcal{E}$, defined in (1.2).

**Proposition 1.4.** *Let $f: X \to Y$ be a map in $\mathfrak{s}\mathcal{E}$. Then $f$ is a (trivial) fibration if and only if, for all $E \in \mathcal{E}$, the map*

$$\text{Hom}_{\mathfrak{sSet}}(E, f): \text{Hom}_{\mathfrak{sSet}}(E, X) \to \text{Hom}_{\mathfrak{sSet}}(E, Y)$$

*is a (trivial) fibration in $\mathfrak{sSet}$.*

6