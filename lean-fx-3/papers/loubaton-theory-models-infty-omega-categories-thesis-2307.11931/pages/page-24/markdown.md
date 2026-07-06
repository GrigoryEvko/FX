Introduction

## On the side of theory

In the second part of this thesis, we will adapt the constructions of classical category theory to the case $(\infty, \omega)$. In this part, we will freely use the language of $(\infty, 1)$-categories$^{1}$.

Chapter 4 is devoted to the basic theory of $(\infty, \omega)$-categories. Chapter 5 introduces the notion of *marked* $(\infty, \omega)$-categories and studies *left Cartesian fibrations*. Chapter 6 is dedicated to the *Grothendieck construction, univalence*, the *Yoneda lemma*, and other standard categorical constructions.

Several of these results, or their analogues in the $(\infty, n)$ setting for some integer $n$, are already present in the literature. The case $n = 1$, i.e. that of $(\infty, 1)$-category theory, is now a prolific research field, and it would be impossible to list all the authors who have contributed to it. Nonetheless, we would like to mention Joyal for his pioneering work ([Joy02]), Lurie for his major contribution ([Lur09a]), and Cisinski ([Cis19]) because his approach has deeply inspired the present work.

For the case $n = 2$, the Grothendieck construction as well as lax limits and colimits have been extensively studied by Gagna, Lanari and Harpaz in [GHL20] and [GHL21], as well as by García and Stern in [GS21] and [GS22].

For arbitrary $n$, Grothendieck construction has been described in [Nui21] and [Ras21]. A partial version of the Yoneda lemma is also present in [Ras21], [Hin21], and [Hei20].

**Chapter 4.** This chapter is dedicated to the basic definition of $(\infty, \omega)$-categories. In the first section, we recall some results on factorization systems in presentable $(\infty, 1)$-categories. In the second section, we define $(\infty, \omega)$-categories and give some basic properties. We also define and study *discrete Conduché functor*, which are morphisms having

$^{1}$As there are currently several directions for the formalization of the language of $(\infty, 1)$-categories ([RV22], [RS17], [Nor19], [CNW]), talking about 'the' language of $(\infty, 1)$-categories may be confusing.

In such case, the reader may consider that we are working within the quasi-category Qcat of **T**-small quasi-categories for **T** a Grothendieck universe. This quasi-category may be obtained either using the coherent nerve as described in [Lur09a, chapter 3], or by considering it as the codomain of the universal co-cartesian fibration with **T**-small fibers as done in [CN22]. In both cases, the straightening/unstraightening correspondence provides a morphism

$$\mathrm{N}(\mathrm{Psh}(\Delta)_\mathbf{T}) \rightarrow \mathrm{Qcat}$$

that exhibits Qcat as the quasi-categorical localization of $\mathrm{N}(\mathrm{Psh}(\Delta)_\mathbf{T})$ with respect to the weak equivalences of the Joyal's model structure ([CN22, theorem 8.13]).

The constructions we use to build new objects - (co)limits of functor between quasi-categories, quasi-categories of functor, localization of quasi-categories, sub maximal Kan complex, full sub quasi-category, adjunction, left and right Kan extension, Yoneda lemma - are well documented in the Joyal model structure (see [Lur09a] or [Cis19]), and therefore have direct incarnation in the quasi-category Qcat.

14