CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

The domain of this arrow is then the colimit of the following diagram:

\[
X (0) ^ {\flat} \times [ a, 1 ] _ {0 /} ^ {\sharp} \longleftarrow X (0) ^ {\flat} \times a ^ {\flat} \longrightarrow X (1) ^ {\flat}
\]

Lemma 6.1.2.6. The functor \(\int_{C}:(\infty ,\omega ,1)\text{-cat}_{/N_{(\omega ,1)}C}\to \mathrm{LCart}(C^{\sharp})\) preserves colimits. Moreover, it sends morphisms of J to equivalences.

Proof. According to corollary 5.2.3.4, it is sufficient to show that the composite

\[
(\infty , \omega , 1) \text {-cat} _ {/ N _ {(\omega , 1)} C} \xrightarrow {\int_ {C}} \operatorname{LCart} (C ^ {\sharp}) \xrightarrow {\operatorname{dom}} (\infty , \omega) \text {-cat} _ {\mathrm{m}}
\]

preserves colimits.

To this extend, we consider the functor

\[
\alpha : \mathrm{Psh} ^ {\infty} (\Theta \times \Delta) _ {/ N _ {(\omega , 1)} C} \to \mathrm{Psh} ^ {\infty} (t \Theta \times \Delta)
\]

sending an object \(E\) of \(\mathrm{LFib}(\mathrm{N}_{(\omega,1)}C)\) corresponding to a morphism \(X\to (\mathrm{N}_{(\omega,1)}C)\) to \(X\times_{(\mathrm{N}_{(\omega,1)}C)^b}C_{/}\), and the functor

\[
\beta : \mathrm{Psh} ^ {\infty} (t \Theta \times \Delta) \to (\infty , \omega) \text {-cat} _ {\mathrm{m}}
\]

that is the left Kan extension of the functor  \( t\Theta \times \Delta \to t\Theta \to \mathrm{mPsh}(\Theta) \) . As  \( \mathrm{Psh}^{\infty}(\Theta \times \Delta) \)  is locally cartesian closed,  \( \alpha \)  preserves colimits. The composite  \( \beta \circ \alpha \)  then preserves colimits. Moreover, we have a commutative diagram

\[
\begin{array}{c} \operatorname{Psh} ^ {\infty} (\Theta \times \Delta) _ {/ N _ {(\omega , 1)} C} \xrightarrow {\beta \circ \alpha} (\infty , \omega) \text {-cat} _ {\mathrm{m}} \\ \mathbf {F} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ (\infty , \omega , 1) \text {-cat} _ {/ N _ {(\omega , 1)} C} \xrightarrow [ \int_ {C} ]{} \operatorname{LCart} (C ^ {\sharp}) \end{array}
\]

According to proposition 6.1.1.4, one then has to show that \(\beta \circ \alpha\) sends any morphism of \(J\) to an equivalence to conclude. Indeed, it will implies that \(\beta \circ \alpha\) lifts to a colimit preserving functor

\[
\mathbf {D} (\beta \circ \alpha): (\infty , \omega , 1) \text {-cat} _ {/ N _ {(\omega , 1)} C} \to (\infty , \omega) \text {-cat} _ {\mathrm{m}},
\]

and the previous square implies that this morphism is equivalent to \(\mathrm{dom}\int_{C}\).

Suppose given two cartesian squares

\[
\begin{array}{c} X \xrightarrow {g} X ^ {\prime} \xrightarrow {} C _ {/} \\ \Big \downarrow \quad \Big \downarrow \quad \Big \downarrow \\ \langle a, \{0 \} \rangle \xrightarrow [ f ]{} \langle a, [ n ] \rangle \longrightarrow (\mathrm{N} _ {(\omega , 1)} C) ^ {b} \end{array}
\]

312