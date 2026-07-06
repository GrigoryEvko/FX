6.2. YONEDA LEMMA AND APPLICATIONS

Proof. Remark that we have an equivalence

$$\hom_{\underline{\mathrm{Hom}}_{\square}(I, \underline{\omega})}(\mathrm{cst}\ 1, \hom_A(a, F(\_))) \sim \hom_{\underline{\omega}}(1, \underset{I}{\mathrm{laxlim}}\hom_A(a, F(\_)))$$

Eventually, the Yoneda lemma implies that

$$\hom_{\underline{\omega}}(1, \underset{I}{\mathrm{laxlim}}\hom_A(a, F(\_)) \sim \underset{I}{\mathrm{laxlim}}\hom_A(a, F(\_)))$$

The result then follows from proposition 6.2.3.17.

Remark 6.2.3.20. The characterization of the lax colimit and limit given in previous corollary is the generalization to the case $(\infty, \omega)$ of the characterization of lax colimit and limit for $(\infty, 2)$-categories given in [GHL20, corollary 5.1.7].

Proposition 6.2.3.21. Let $i: I \to J$ and $F: J \to A^\sharp$ be two morphisms between U-small marked $(\infty, \omega)$-categories. If $i$ is initial, and $F$ admits a lax limit, the functor $F \circ i$ also admits a lax limit, and the canonical morphism:

$$\underset{I}{\mathrm{laxlim}}\ F \to \underset{J}{\mathrm{laxlim}}\ F \circ i$$

is an equivalence. Dually, if $i$ is final, and $F$ admits a lax colimit, the functor $F \circ i$ also admits a lax colimit, and the canonical morphism:

$$\underset{J}{\mathrm{laxcolim}}\ F \circ i \to \underset{I}{\mathrm{laxlim}}\ F$$

is an equivalence.

Proof. The first assertion is a direct application of the characterization of limits given in proposition 6.2.3.17 and of proposition 6.2.3.15. The second assertion follows by duality.

The proof of the following lemma is a direct adaptation of the one of proposition 5.1 of [GHN].

Proposition 6.2.3.22. Let $f: A \to B$ be any morphism between U-small $(\infty, \omega)$-categories.. There is an equivalence

$$\hom_{\underline{\mathrm{Hom}}(A, B)}(f, g) \sim \underset{a \to b: S(A)}{\mathrm{laxlim}}\hom_B(f(a), g(a))$$

natural in $f$ and $g$.

Proof. Remark first that the left term is in fact equivalent to

$$\underset{a \to b: S(A)}{\mathrm{laxlim}}\ h^*\hom_B(\_, \_)$$

357