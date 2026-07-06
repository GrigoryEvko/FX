CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

Proposition 5.1.1.17. The cartesian product in \((\infty, \omega)\)-cat$_{\mathrm{m}}$ preserves colimits in both variables.

Proof. Let  \( F: I \to (\infty, \omega) \) -cat \( _{m} \)  be a diagram and C a marked  \( (\infty, \omega) \) -category. The underlying  \( (\infty, \omega) \) -categories of  \( \operatorname{colim}_{I}(F \times C) \)  and  \( (\operatorname{colim}_{I} F) \times C \)  are the same as the cartesian product preserves colimits in  \( (\infty, \omega) \) -cat. The equivalence of the two markings is a direct consequence of the fact that the cartesian product in  \( \infty \) -grd preserves both colimits and the formation of image. □

This demonstrates the existence of an internal hom functor that we denote once again by \(\underline{\mathrm{Hom}} (\_, \_)\).

5.1.1.18. We denote again  \( \pi_{0}:\mathrm{tPsh}^{\infty}(\Theta)\to\mathrm{tPsh}(\Theta) \)  colimit preserving sending a stratified  \( \infty \) -presheaf X to the stratified presheaf  \( a\mapsto\pi_{0}(X_{a}) \) . As this functor preserves tW, it induces an adjoint pair:

\[
\pi_ {0}: (\infty , \omega) \text {-cat} \xrightarrow [ \leftarrow ]{\perp} (0, \omega) \text {-cat}: N
\]

where the right adjoint N is fully faithful. A marked  \( (\infty,\omega) \) -category lying in the image of the nerve is called strict. Remark eventually that the following square is cartesian

\[
\begin{array}{c} (0, \omega) \text {-cat} _ {\mathrm{m}} \xrightarrow {\mathrm{N}} (\infty , \omega) \text {-cat} _ {\mathrm{m}} \\ (\_) ^ {\natural} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ (0, \omega) \text {-cat} \xrightarrow {\mathrm{N}} (\infty , \omega) \text {-cat} \end{array}
\]

A marked \((\infty, \omega)\)-category is then strict if and only if it's underlying \((\infty, \omega)\)-category is.

5.1.1.19. The marked suspension is the colimit preserving functor

\[
[ \_, 1 ]: (\infty , \omega) \text {-cat} _ {\mathrm{m}} \to (\infty , \omega) \text {-cat} _ {\mathrm{m} _ {\bullet , \bullet}}
\]

sending \(a^{\flat}\) onto \([a,1]^{\flat}\) and \((\mathbf{D}_n)_t\) to \(([\mathbf{D}_n,1])_t\). It then admits a right adjoint:

\[
\begin{array}{l} (\infty , \omega) \text {-cat} _ {\mathrm{m} _ {\bullet , \bullet}} \to (\infty , \omega) \text {-cat} _ {\mathrm{m}} \\ (C, a, b) \qquad \mapsto \hom_ {C} (a, b) \\ \end{array}
\]

With the same computation than the one of paragraph 4.2.1.17, we show that for a marked \((\infty, \omega)\)-category \(C\), any 1-cell \(f: x \to x'\) induces for any object \(y\), a morphism

\[
f _ {!}: \hom_ {C} (x ^ {\prime}, y) \to \hom_ {C} (x, y).
\]

Conversely, a 1-cell \( g: y \to y' \) induces for any object \( x \) a morphism

\[
g _ {!}: \hom_ {C} (x, y) \to \hom_ {C} (x, y ^ {\prime})
\]

238