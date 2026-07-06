CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Proof. The proposition 3.2.1.9 implies that \((\overline{[1] \star [a, 1]})_{\mathrm{mk}}\) is the colimit of the diagram

\[
\begin{array}{c} \left[ [ 2 ] ^ {2} \bar {\otimes} a, 1 \right] \xleftarrow {[ d ^ {0} \otimes a , 1 ]} \left[ [ 1 ] _ {t} \otimes a, 1 \right] \xrightarrow {[ [ 1 ] \otimes a , d ^ {1} ]} \left[ [ 1 ] _ {t}, 1 \right] \vee [ a, 1 ] \xleftarrow {[ d ^ {0} \otimes a , 2 ]} [ e, 1 ] \vee [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ e, 2 ] \vee [ a, 1 ] \\ [ d ^ {1} \bar {\otimes} a, 1 ] \uparrow \\ [ e \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ d ^ {0} \star a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ e, 1 ] \vee [ a, 1 ] \\ [ d ^ {1} \star a, 1 ] \downarrow \\ [ [ 1 ] \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ d ^ {0} \star a, 1 ] \downarrow \\ [ e \star a, 1 ] \xrightarrow [ [ e \star a , d ^ {1} ] ]{} [ e, 1 ] \vee [ e \star a, 1 ] \end{array} \tag {3.2.3.4}
\]

In the previous diagram, the fact that we have \([ [1]_t \otimes a, 1]\) instead of \([ [1] \otimes a, 1]\) comes from the fact that we have considered \((\overline{[1] \star [a, 1]})_{\mathrm{mk}}\) instead of \(\overline{[1] \star [a, 1]}\).

Consider now the morphism

\[
[ [ 2 ] ^ {2} \bar {\otimes} a, 1 ] \coprod_ {[ [ 1 ] _ {t} \otimes a, 1 ]} [ [ 1 ] _ {t}, 1 ] \vee [ a, 1 ] \rightarrow e \star [ a, 1 ] \tag {3.2.3.5}
\]

induces by the vertical colimit of the diagram

\[
\begin{array}{c} \left[ [ 2 ] ^ {2} \bar {\otimes} a, 1 \right] \xleftarrow {[ d ^ {0} \otimes a , 1 ]} \left[ [ 1 ] _ {t} \otimes a, 1 \right] \xrightarrow {[ [ 1 ] \otimes a , d ^ {1} ]} \left[ [ 1 ] _ {t}, 1 \right] \vee [ a, 1 ] \\ \left[ s ^ {0} \bar {\otimes} a, 1 \right] \Bigg \downarrow \quad \Bigg \downarrow \left[ s ^ {0} \otimes a, 1 \right] \quad \Bigg \downarrow \left[ s ^ {0}, 1 \right] \vee [ a, 1 ] \\ [ e \star a, 1 ] \xleftarrow {} [ a, 1 ] \longrightarrow [ e, 1 ] \vee [ a, 1 ] \end{array} \tag {3.2.3.6}
\]

As all the horizontal morphisms of (3.2.3.6) are cofibrations, the colimit of each line is a homotopy colimit. As all the vertical morphisms of (3.2.3.6) are weak equivalences, the morphism (3.2.3.5) also is a weak equivalence.

Consider now the span

\[
e \star [ a, 1 ] \xleftarrow {(3 . 2 . 3 . 5)} [ [ 2 ] ^ {2} \bar {\otimes} a, 1 ] \coprod_ {[ [ 1 ] _ {t} \otimes a, 1 ]} [ [ 1 ] _ {t}, 1 ] \vee [ a, 1 ] \rightarrow (\overline {{[ 1 ] \star [ a , 1 ]}}) _ {\mathrm{mk}} \tag {3.2.3.7}
\]

As the right hand morphism is a cofibration, and as (3.2.3.5) is a weak equivalence, the canonical morphism from \((\overline{[1] \star [a, 1]})_{\mathrm{mk}}\) to the colimit of (3.2.3.7) is a weak equivalence. Using the diagram (3.2.3.4), the colimit of (3.2.3.7) is also the colimit of the following diagram

\[
\begin{array}{c} e \star [ a, 1 ] \xleftarrow {} [ e, 1 ] \vee [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ e, 2 ] \vee [ a, 1 ] \\ \uparrow \quad \text {   } \quad [ a, d ^ {1} ] \uparrow \quad \uparrow [ a, d ^ {2} ] \\ [ e \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ e, 1 ] \vee [ a, 1 ] \\ [ d ^ {1} \star a, 1 ] \downarrow \quad [ d ^ {0} \star a, 1 ] \downarrow \quad \downarrow [ d ^ {0} \star a, 2 ] \\ [ [ 1 ] \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ e \star a, 1 ] \xrightarrow [ [ e \star a , d ^ {1} ] ]{} [ e, 1 ] \vee [ e \star a, 1 ] \end{array} \tag {3.2.3.8}
\]

As the upper left square is cocartesian, the colimit of the diagram 3.2.3.8 is equivalent to the colimit of the diagram

\[
\begin{array}{c} \left[ e, 2 \right] \vee [ a, 1 ] \\ \uparrow [ a, d ^ {2} ] \\ \left[ e, 1 \right] \vee [ a, 1 ] \\ \downarrow [ d ^ {0} \star a, 2 ] \\ \left[ [ 1 ] \star a, 1 \right] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ e \star a, 1 ] \xrightarrow [ [ e \star a , d ^ {1} ] ]{} [ e, 1 ] \vee [ e \star a, 1 ] \end{array} \tag {3.2.3.9}
\]

120