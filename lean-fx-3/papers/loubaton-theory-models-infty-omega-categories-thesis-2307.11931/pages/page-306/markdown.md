CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

LCart(A\( ^{\sharp} \); b). As both \( i_{!} \) and \( i^{*} \) preserve cartesian lifting according to lemma 5.2.5.15, they induce by Grothendieck deconstruction a family of adjunction

\[
(i _ {a}) _ {!}: \operatorname{LCart} ^ {c} (I; a) \xrightarrow [ \leftarrow ]{\perp} \operatorname{LCart} \left(A ^ {\sharp}; a\right): \left(i _ {a}\right) ^ {*} \tag {5.2.5.16}
\]

natural in \(a:\Theta^{op}\). The family of functors \((i_a)_!\) then induces a morphism of \((\infty ,\omega)\)-category

\[
i _ {!}: \underline {{\mathrm{LCart}}} ^ {c} (I) \rightarrow \underline {{\mathrm{LCart}}} (A ^ {\sharp}) \tag {5.2.5.17}
\]

which corresponds to  \( \mathbf{L}i_{!}:\mathrm{LCart}^{c}(I)\to\mathrm{LCart}(A^{\sharp}) \)  on the maximal sub  \( (\infty,1) \) -category. The unit and counit of adjunction (5.2.5.16) induce morphisms

\[
\mu : i d \rightarrow i ^ {*} i _ {!} \quad \epsilon : i _ {!} i ^ {*} \rightarrow i d \tag {5.2.5.18}
\]

and equivalences \((\epsilon \circ_0 i_!) \circ_1 (i_! \circ_0 \mu) \sim id_{i_!}\) and \((i^* \circ_0 \epsilon) \circ_1 (\mu \circ_0 i^*) \sim id_{i^*}\).

5.2.5.19. Let \( j: C^{\sharp} \to D^{\sharp} \) be a morphism between \( (\infty, \omega) \)-categories. We claim that the commutative square

\[
\begin{array}{c} \underline {{\mathrm{LCart}}} (D ^ {\sharp} \times A ^ {\sharp}) \xrightarrow {(i d _ {D ^ {\sharp}} \times i) ^ {*}} \underline {{\mathrm{LCart}}} ^ {c} (D ^ {\sharp} \times I) \\ (j \times i d _ {A ^ {\sharp}}) ^ {*} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow (j \times i d _ {I}) ^ {*} \\ \underline {{\mathrm{LCart}}} (C ^ {\sharp} \times A ^ {\sharp}) \xrightarrow {(i d _ {C ^ {\sharp}} \times i) ^ {*}} \underline {{\mathrm{LCart}}} ^ {c} (C ^ {\sharp} \times I) \end{array}
\]

induces a commutative square

\[
\begin{array}{c} \underline {{\mathrm{LCart}}} ^ {c} (D ^ {\sharp} \times I) \xrightarrow {(j \times i d _ {I}) ^ {*}} \underline {{\mathrm{LCart}}} ^ {c} (C ^ {\sharp} \times I) \\ (i d _ {D ^ {\sharp}} \times i)! \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow (i d _ {C ^ {\sharp}} \times i)! \\ \underline {{\mathrm{LCart}}} (D ^ {\sharp} \times A ^ {\sharp}) \xrightarrow {(j \times i d _ {A ^ {\sharp}}) ^ {*}} \underline {{\mathrm{LCart}}} (C ^ {\sharp} \times A ^ {\sharp}) \end{array} \tag {5.2.5.20}
\]

A priori, the natural transformations (5.2.5.18) implies that this square commutes up the natural transformation:

\[
\begin{array}{l} (i d _ {C ^ {\sharp}} \times i) _ {!} \circ (j \times i d _ {I}) ^ {*} \rightarrow (i d _ {C ^ {\sharp}} \times i) _ {!} \circ (j \times i d _ {I}) ^ {*} \circ (i d _ {D ^ {\sharp}} \times i) ^ {*} \circ (i d _ {D ^ {\sharp}} \times i) _ {!} \\ \sim \quad (i d _ {C ^ {\sharp}} \times i) _ {!} \circ (i d _ {C ^ {\sharp}} \times i) ^ {*} \circ (j \times i d _ {A ^ {\sharp}}) ^ {*} \circ (i d _ {D ^ {\sharp}} \times i) _ {!} \\ \rightarrow (j \times i d _ {A ^ {\sharp}}) ^ {*} \circ (i d _ {D ^ {\sharp}} \times i)! \\ \end{array}
\]

Proposition 5.2.4.24 implies that this natural transformation is pointwise an equivalence, and so is globally an equivalence.

296