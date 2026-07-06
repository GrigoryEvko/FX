CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

where  \( \pi \)  is the projection  \( [[n-2],2]\to[e,1]\vee[[n-2],1] \) . However, according to the diagrams (5) and (3) of 3.3.3.2, there is a diagram:

\[
\begin{array}{c} \left[ [ 1 ] \otimes [ n - 2 ], 1 \right] \xrightarrow {\left[ [ 1 ] \otimes [ n - 2 ] , d _ {1} ^ {1} \right]} [ e \star [ n - 2 ], 1 ] \vee \left[ [ n - 2 ], 1 \right] \xleftarrow {e \star [ n - 2 ] , d ^ {2}} [ e \star [ n - 2 ], 1 ] \\ [ d ^ {0} \otimes [ n - 2 ], 1 ] \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Biggl \downarrow \delta_ {[ n - 2 ]} \qquad \qquad \qquad \Biggl \downarrow \alpha_ {[ n - 2 ]} \\ \left[ [ 2 ] \bar {\otimes} [ n - 2 ], 1 \right] \xrightarrow {\epsilon_ {[ n - 2 ]}} \left[ [ n - 2 ], 2 \right] \xleftarrow {} e \star [ [ n - 2 ], 1 ] \\ \Biggl \downarrow e \star \pi \qquad \qquad \qquad \Biggl \downarrow \\ e \star ([ e, 1 ] \vee [ [ n - 2 ], 1 ]) \xleftarrow {} e \star [ e, 1 ] \\ \tau_ {1} \circ e \star \beta_ {[ n - 1 ]} \Biggl \downarrow \qquad \qquad \qquad \Biggl \downarrow \\ [ n + 1 ] ^ {1} \xleftarrow [ d ^ {3} \circ .. \circ d ^ {n + 1} ]{} [ 2 ] _ {t} \end{array}
\]

This implies that \([[2]\bar{\otimes}[n - 2],1]\to [n + 1]^k\to ([n + 1]^k)_{\mathrm{mk}}\) factors through \([[2]\bar{\otimes}[n - 2]\coprod_{d^0\otimes a}\tau_{n - 1}^t ([1]\otimes [n - 2]),1]\). We can then apply lemma 3.3.3.10.

Lemma 3.3.3.19. Let \(0 < k < n - 1\) be two integers. We denote by \(\tau^k\) the projection \([n] \to [n]^k\). We then have

\[
\left(\tau^ {k} \circ \iota_ {n} \circ [ d ^ {k - 1}, 1 ], \tau^ {k} \circ \iota_ {n} \circ [ d ^ {k + 1}, 1 ]\right) \geq_ {n - 1} \tau^ {k} \circ \iota_ {n} \circ [ d ^ {k}, 1 ]
\]

and

\[
\tau^ {n - 1} \circ \iota_ {n} \circ [ d ^ {n - 2}, 1 ] \geq_ {n - 1} \tau^ {k} \circ \iota_ {n} \circ [ d ^ {n - 1}, 1 ].
\]

Proof. By construction, for any \(a\), the morphism \([(2] \star a, 1] \to [2] \star [a, 1] \to [2]_t \star [a, 1]\) factors through \([(2]_t \star a, 1]\). By induction, this implies that the composite morphism \([(n-1], 1] \xrightarrow{\iota_n} [n] \to [n]^k\) factors through \([(n-1]^k, 1]\) for any \(k < n-1\). This implies the first assertion.

For the second one, note that  \( [[1], e] \to [2] \to [2]_{t} \)  factors through  \( [[1]_{t}, e] \) . By induction, this implies that the composite morphism  \( [[n-1], 1] \xrightarrow{\iota_{n}} [n] \to [n]^{n-1} \)  factors through  \( [[n-1]^{n-2}, 1] \)  which gives the second one. □

Proposition 3.3.3.20. For any \(0 \leq k \leq n\), the morphism \(([n]^k)' \to ([n]^k)''\) is a weak equivalence.

Proof. The case k = 0 and k = n are demonstrated in lemma 3.3.3.1. For the case  \( 0 < k < n \) , lemmas 3.3.3.17, 3.3.3.18 and 3.3.3.19 imply that if we denote by  \( \tau_{k} \)  the projection  \( [n] \to [n]^{k} \) , we have an inequality:  \( (\tau_{k} \circ d^{k-1} \circ \iota_{n-1}, \tau_{k} \circ d^{k+1} \circ \iota_{n-1}) \geq_{n-1} \tau_{k} \circ d^{k} \circ \iota_{n-1} \) . Together with the proposition 3.3.3.8, this implies that the following square is homotopy cartesian:

\[
\begin{array}{c} [ n - 1 ] \cup [ n - 1 ] \xrightarrow {d ^ {k + 1} \cup d ^ {k - 1}} [ n ] ^ {k} \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ [ n - 1 ] _ {t} \cup [ n - 1 ] _ {t} \longrightarrow ([ n ] ^ {k}) ^ {\prime \prime} \end{array}
\]

160