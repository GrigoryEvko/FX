Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:3

1.2. Internalizing the power of presheaves. Purely metatheoretic results about type theory certainly have their value. Parametricity, for instance, has originated and proven its value as a metatheoretic technique for reasoning about programs. However, with dependent type theory being not only a programming language but also a logic, it is preferable to formulate results about it within the type system, rather than outside it. We highlight two particular motivations for doing so: to enlarge the end user's toolbox, and to be able to prove internally that a type is fibrant.

Enlarging the end user's toolbox. One motivation for internalizing metatheorems is to enlarge the toolbox of the end user of the proof assistant. If this is the only goal, then we can prove the desired results in the model on pen and paper and then internalize them ad hoc with an axiom with or without computation rules.

HoTT: Book HoTT [Uni13] simply postulates the univalence axiom without computational behaviour, as justified e.g. by the model of Kan-fibrant simplicial sets [KL18].

CCHM cubical type theory [CCHM17] provides the Glue type, which comes with introduction, elimination, β- and η-rules and which turns the univalence axiom into a theorem with computational behaviour. It also contains CCHM-Kan-fibrancy of all types as an axiom, in the form of the CCHM-Kan composition operator, with decreed computational behaviour that is defined by induction on the type.

Parametricity: Bernardy, Coquand and Moulin [BCM15, Mou16] (henceforth: BCM) internalize their (unary, but generalizable to k-ary) cubical set model of parametricity using two combinators Φ and Ψ [Mou16], a.k.a. extent and Gel [CH21]. Φ internalizes the presheaf structure of the function type, and Ψ that of the universe.

The combinator Φ and at first sight also Ψ require that the cubical set model lacks diagonals. Indeed, to construct a value over the primitive interval, Φ and Ψ each take one argument for every endpoint and one argument for the edge as a whole. Nested use of these combinators, e.g. to create a square, will take (k + 1)² arguments for k² vertices, 2k sides and 1 square as a whole but none for specifying the diagonal. For this reason, BCM's type system enforces a form of affine use of interval variables. Similarly, connections as in CCHM [CCHM17] are ruled out. In the current paper, we will see that these requirements are not absolute for Ψ: there is apparently a very natural 'automatic' way to define the behaviour on diagonals and connections where the Ψ-type is not explicitly specified by its arguments.

In earlier work with Vezzosi [NVD17], we have internalized parametricity instead using the Glue type [CCHM17] and its dual Weld. Later on, we added a primitive mill [ND18b] for swapping Weld and Π(i : 𝕀). These operations are sound in presheaves over any base category where we can multiply with 𝕀 – including cube categories with diagonals or connections – and are (therefore) strictly less expressive than Φ which is not. Discreteness of all types was internalized as a non-computing path degeneracy axiom.²

²It is worth noting that it was not possible to use affine interval variables in the setting of [NVD17]: The type system features parametric Π-types which are modelled as ordinary Π-types with non-discrete domain. Discreteness of the Π-type can be proven solely from discreteness of the codomain, simply by swapping interval variable and function argument. This is however not possible in the affine setting, where only variables introduced prior to an interval variable are taken to be fresh for that interval variable and the exchange rule with an interval variable only works one way.