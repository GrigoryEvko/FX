**Theorem 1.2.3.13.** *In the category of $(0, \omega)$-categories, there exists an isomorphism, natural in $A$, between $[A, 1] \otimes [1]$ and the colimit of the following diagram*

$$[1] \vee [A, 1] \xleftarrow{\nabla} [A \otimes \{0\}, 1] \longrightarrow [A \otimes [1], 1] \longleftarrow [A \otimes \{1\}, 1] \xrightarrow{\nabla} [A, 1] \vee [1]$$

We also provide similar formulas for the *Gray cone* and the *Gray $\circ$-cone*.

**Theorem 1.2.3.14.** *There is a natural identification between $1 \stackrel{\circ}{\star} [A, 1]$ and the colimit of the following diagram*

$$[1] \vee [A, 1] \xleftarrow{\nabla} [A, 1] \longrightarrow [A \star 1, 1]$$

*There is a natural identification between $[A, 1] \star 1$ and the colimit of the following diagram*

$$[1 \stackrel{\circ}{\star} A, 1] \longleftarrow [A, 1] \xrightarrow{\nabla} [A, 1] \vee [1]$$

## On the side of models

Following the terminology of Barwick and Schommer-Pries ([BSP21]), we call *model of $(\infty, n)$-categories* any model category whose corresponding $(\infty, 1)$-category is $(\infty, n)$-cat.

With the definition of $(\infty, n)$-categories given above, we have a natural model for the $(\infty, 1)$-category $(\infty, n)$-cat, given by Rezk's complete Segal $\Theta_n$-spaces, i.e. space valued presheaves on $\Theta_n$ satisfying the (homotopical) Segal conditions and (homotopical) completeness conditions. However, there are many other models, see for instance [Ara14], [BR13a], [BR20], [BR13b] (we refer to [BSP21] for a comprehensive presentation of these models and their equivalences). For example, one can mention $n$-fold Segal spaces and Simpson's and Tamsamani's Segal $n$-categories among others.

It was conjectured ([Str87], [Ver17], [BSP21]) that Verity's $n$-complicial sets were also a model of $(\infty, n)$-categories. This would imply that Campion-Kapulkin-Maehara's $n$-comical sets also are, as they are shown to be Quillen equivalent to $n$-complicial sets in [DKM21]. In the second chapter, we will give a positive answer to this conjecture (theorem 3.4.3.2).

One of the major consequences of this result is to endow $(\infty, \omega)$-cat with a monoidal product called the *Gray tensor product*. This operation will play a crucial role in the second part of this thesis, which is dedicated to the theory of $(\infty, \omega)$-categories.

The two main models we work with are Verity's complicial sets (definition 2.2.1.5) and (a slight modification of) Segal $A$-precategories (defined in paragraph 3.1.1.6) as developed by Simpson ([Sim11]). In the complicial model, we will make crucial use of the strictification results of Ozornova and Rovelli ([OR20a], [OR22]).

11