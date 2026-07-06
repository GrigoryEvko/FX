CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Lemma 3.1.2.9. A morphism \( f \) has the right lifting property against \( J \) if and only if \( f^{\sharp} \) is a fibration and \( f \) has the right lifting property against \( [e,1]_t \to [e,E^{eq}]^{\sharp} \) and \( [e,E^{eq}] \to [e,E^{eq}]^{\sharp} \). An object \( X \) has the right lifting property against \( J \) if and only if it is a marked Segal \( A \)-category.

Proof. Straightforward.

Lemma 3.1.2.10. Let \(i: K \to L\) be a cofibration that induces an isomorphism on objects. The morphism

\[
K \times [ e, E ^ {e q} ] \coprod_ {K \times [ e, 1 ]} L \times [ e, 1 ] \rightarrow L \times [ e, E ^ {e q} ]
\]

is an acyclic cofibration of the model structure on \(\operatorname{Seg}(A)\).

Proof. By two out of three, and some diagram chasing, is it sufficient to demonstrate the result for \( K \) being \( L_0 \). We then have to show that the square

\[
\begin{array}{c} L _ {0} \times [ e, 1 ] \longrightarrow L \times [ e, 1 ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ L _ {0} \times [ e, E ^ {e q} ] \longrightarrow L \times [ e, E ^ {e q} ] \end{array}
\]

is homotopy coccartesian. As the model structure is cartesian, and as \([e,E^{eq}]\to 1\) is a weak equivalence, this is sufficient to show that the following square is homotopy cocartesian:

\[
\begin{array}{c} L _ {0} \times [ e, 1 ] \longrightarrow L \times [ e, 1 ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ L _ {0} \longrightarrow L \end{array}
\]

As \(\_ \times [e,1]\) and \(\_ \times [e,E^{eq}]\) are left Quillen functors, we can reduce to the case where \(L\) is \([a,n]\) and using Segal extension, to the case where \(L\) is \([a,1]\). We then have to show that the following square is homotopy cocartesian

\[
\begin{array}{c} \left(\{0 \} \cup \{1 \}\right) \times [ e, 1 ] \longrightarrow [ a, 1 ] \times [ e, 1 ] \\ \Biggl \downarrow \quad \Biggl \downarrow \\ \{0 \} \cup \{1 \} \longrightarrow [ a, 1 ] \end{array} \tag {3.1.2.11}
\]

Remark then that  \( [a,1]\times[e,1] \)  is the colimit of the following span:

\[
[ e, 1 ] \vee [ a, 1 ] \xleftarrow {[ a , d ^ {1} ]} [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ a, 1 ] \vee [ e, 1 ]
\]

The pushout of the span of (3.1.2.11) is then the (homotopy) colimit of

\[
[ 0 ] \coprod_ {[ e, 1 ]} [ e, 1 ] \vee [ a, 1 ] \xleftarrow {[ a , d ^ {1} ]} [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ a, 1 ] \vee [ e, 1 ] \coprod_ {[ e, 1 ]} [ 0 ]
\]

By two out of three, and using Segal extensions, the two morphisms

\[
[ 0 ] \coprod_ {[ e, 1 ]} [ e, 1 ] \vee [ a, 1 ] \rightarrow [ a, 1 ] \quad \text { and } \quad [ a, 1 ] \vee [ e, 1 ] \coprod_ {[ e, 1 ]} [ 0 ] \rightarrow [ a, 1 ]
\]

induced by  \( [a,d^{0}] \)  and  \( [a,d^{2}] \)  are weak equivalences. In particular, this implies that the canonical morphism from the pushout of the span of (3.1.2.11) to  \( [a,1] \)  is a weak equivalence. As the upper horizontal vertical morphisms of (3.1.2.11) is a cofibration, this implies that this square is homotopy cocartesian which concludes the proof.

106