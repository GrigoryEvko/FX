CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

This implies that \( r_{e\star([\tau_{n-1}^i(a),1]\vee [a,1])}\circ e\star \pi' \circ e\star [a,d^2]\circ \alpha_a \) factors through \( [\tau_n^i (e\star a),1] \). The morphism \( r_{e\star ([\tau_{n-1}^i(a),1]\vee [a,1])}\circ e\star \pi \circ \epsilon_a \) then factors through \( [[2]\otimes a\coprod_{d^0\otimes a}\tau_n^i ([1]\otimes a),1] \). According to lemma 3.2.4.10, we then get the second inequality.

Lemma 3.2.4.12. Let \( n \) be an integer strictly superior to 1 and \( a \) such that \( \tau_n^i(a) = a \). We then have \( \delta_a \circ [e \star a, d^2] \geq_{n+1} \delta_a \circ [[1] \otimes a, d^1] \).

Proof. There is a diagram:

\[
\begin{array}{c} [ e \star a, 1 ] \xrightarrow {i d} [ e \star a, 1 ] \xleftarrow {} [ [ 1 ] \otimes a, 1 ] \\ \Big \downarrow [ e \star a, d ^ {2} ] \qquad \qquad \qquad \Big \downarrow [ [ 1 ] \otimes a, d ^ {2} ] \\ e \star [ a, 2 ] \xleftarrow [ \delta_ {a} ] {\delta_ {a}} [ e \star a, 1 ] \vee [ a, 1 ] \xleftarrow {} [ [ 1 ] \otimes a, 1 ] \vee [ a, 1 ] \\ \Big \uparrow [ [ 1 ] \otimes a, d ^ {1} ] \qquad \qquad \qquad \Big \uparrow [ [ 1 ] \otimes a, d ^ {1} ] \\ [ [ 1 ] \otimes a, 1 ] \xleftarrow [ i d ] {i d} [ [ 1 ] \otimes a, 1 ] \end{array}
\]

As the morphism \([ [1] \otimes a, 1] \vee [a, 1] \to [e \star a, 1] \vee [a, 1]\) factors through \([ [1] \otimes a, 1] \vee [\tau_n^i ([1] \otimes a), 1]\), we get the desired inequality.

Proposition 3.2.4.13. Let \( a \) be an object such that \( \tau_n^i(a) = a \). Let \( x: [a,1] \to C, y: [a',1] \to C \) be two morphisms, such that \( x \geq_n y \), then if we denote by \( \bar{x} := e \star x \circ \alpha_a \) and \( \bar{y} := e \star y \circ \alpha_{a'} \), we have \( \bar{x} \geq_{n+1} \bar{y} \).

Proof. First, we suppose that we are in the first case of the definition 3.2.4.5. We can then suppose without loss of generality that \( C = [a,1] \vee [\tau_{n-1}^i(a),1] \). We denote by \( \pi \) the projection of \( [a,2] \) on \( [a,1] \vee [\tau_{n-1}^i(a),1] \). Using the diagrams (3).3.2.4.2, (4).3.2.4.2 and (5).3.2.4.2, we have a diagram:

\[
\begin{array}{c} [ [ 1 ] \otimes a, 1 ] \xrightarrow {[ d ^ {0} \otimes a , 1 ]} [ [ 2 ] \bar {\otimes} a, 1 ] \xleftarrow {[ d ^ {1} \bar {\otimes} a , 1 ]} [ e \star a, 1 ] \\ [ [ 1 ] \otimes a, d ^ {1} ] \Big \downarrow \qquad \qquad \qquad \Big \downarrow \epsilon_ {a} \qquad \qquad \qquad \Big \downarrow \alpha_ {a} \\ [ e \star a, 1 ] \vee [ a, 1 ] \xrightarrow {\delta_ {a}} e \star [ a, 2 ] \xleftarrow {e \star [ a , d ^ {1} ]} e \star [ a, 1 ] \\ [ e \star a, d ^ {2} ] \Big \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ e \star a, 1 ] \xrightarrow {\alpha_ {a}} e \star [ a, 1 ] \qquad \qquad \qquad e \star ([ a, 1 ] \vee [ \tau_ {n - 1} ^ {i} (a), 1 ]) \end{array}
\]

Thanks to lemmas 3.2.4.11 and 3.2.4.12, this implies the result.

If we are in the second case of 3.2.4.5, we can suppose that \( C = [\tau_{n-1}^i(a), 1] \vee [a, 1] \), and we note by \( \pi' \) the projection from \( [a, 2] \to [\tau_{n-1}^i(a), 1] \vee [a, 1] \). Using the diagrams (4).3.2.4.2 and (6).3.2.4.2, we have a diagram:

\[
\begin{array}{c} [ e \star a, 1 ] \xrightarrow {[ d ^ {2} \bar {\otimes} a , 1 ]} [ [ 2 ] \bar {\otimes} a, 1 ] \xleftarrow {[ d ^ {1} \bar {\otimes} a , 1 ]} [ e \star a, 1 ] \\ \alpha_ {a} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star [ a, 1 ] \xrightarrow [ e \star [ a , d ^ {0} ] ]{} e \star [ a, 2 ] \xleftarrow [ e \star [ a , d ^ {1} ] ]{} e \star [ a, 1 ] \\ \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star ([ \tau_ {n - 1} ^ {i} (a), 1 ] \vee [ a, 1 ]) \end{array}
\]

Thanks to lemmas 3.2.4.11, this implies the result.

If we are in the third case, it is a direct consequence of the naturality of \(\alpha\), of the definition of \(n\)-reliability and of the fact that \((e \star C)_{\mathrm{mk}} \cong (e \star C_{\mathrm{mk}})_{\mathrm{mk}}\) as remarked in 3.2.3.1.

130