4.2. BASIC CONSTRUCTIONS

4.2.1.20. Suppose given an  \( (\infty,\omega) \) -category C and a 1-cells  \( f:x'\to x \) . As C is an  \( (\infty,\omega) \) -category, for any globular sum a, the morphism

\[
\mathrm{Hom} ([ 1 ] \vee [ a, 1 ], C) \to \mathrm{Hom} ([ 1 ], C) \times_ {\mathrm{Hom} ([ 0 ], C)} \mathrm{Hom} ([ a, 1 ], C)
\]

is an equivalence. This induces a morphism

\[
\mathrm{Hom} (a, \mathrm{hom} _ {C} (x, y)) \to \mathrm{Hom} ([ 1 ] \vee [ a, 1 ], (C, x ^ {\prime}, y)) \to \mathrm{Hom} (a, \mathrm{hom} _ {C} (x ^ {\prime}, y))
\]

where the two distinguished points of  \( [1] \vee [a,1] \)  are the extremal ones, and where the left-hand morphism is the restriction of the inverse of the previous morphism. By the Yoneda lemma, this corresponds to a morphism

\[
f _ {!}: \hom_ {C} (x ^ {\prime}, y) \to \hom_ {C} (x, y).
\]

Conversely, a 1-cell \( g: y \to y' \) induces a morphism

\[
g _ {!}: \hom_ {C} (x, y) \to \hom_ {C} (x, y ^ {\prime}).
\]

4.2.1.21. We denote by \(\iota\) the inclusion of \((\infty, \omega)\)-cat into \(\mathrm{Psh}^{\infty}(\Theta)\). A functor \(F: I \to (\infty, \omega)\)-cat has a special colimit if the canonical morphism

\[
\underset {i: I} {\operatorname{colim}} \iota F (i) \rightarrow \iota (\underset {i: I} {\operatorname{colim}} F (i)) \tag {4.2.1.22}
\]

is an equivalence of presheaves.

Similarly, we say that a functor \(\psi : I \to \mathrm{Arr}((\infty, \omega)\text{-cat})\) has a special colimit if the canonical morphism

\[
\underset {i: I} {\operatorname{colim}} \iota \psi (i) \to \iota (\underset {i: I} {\operatorname{colim}} \psi (i))
\]

is an equivalence in the arrow  \( (\infty,1) \) -category of  \( \mathrm{Psh}^{\infty}(\Theta) \) .

Example 4.2.1.23. Let C be an  \( (\infty,\omega) \) -category. The canonical diagram  \( \Theta_{/C} \to (\infty,\omega) \) -cat has a special colimit, given by C.

Proposition 4.2.1.24. Let \( F, G: I \to (\infty, \omega) \)-cat be two functors, and \( \psi: F \to G \) a natural transformation. If \( \psi \) is cartesian, and \( G \) has a special colimit, then \( \psi \) and \( F \) have special colimits.

Proof. We have to show that \( F \) has a special colimit, it will directly imply that \( \psi \) also has one. The morphism (4.2.1.22) is always in \( \widehat{\mathrm{W}} \). To conclude, one then has to show that \( \operatorname{colim}_{i:I} \iota \psi(i) \) is W-local. To this extend, it is enough to demonstrate that the canonical morphism

\[
\underset {i: I} {\operatorname{colim}} \iota \psi (i): \underset {i: I} {\operatorname{colim}} \iota F (i) \to \underset {i: I} {\operatorname{colim}} \iota G (i)
\]

189