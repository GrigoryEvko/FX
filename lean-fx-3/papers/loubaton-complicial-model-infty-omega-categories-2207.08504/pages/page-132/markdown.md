CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Proof. We start by showing the first inequality by induction on \( n \). If \( n = 2 \), the only case is \( k = 1 \), and the two morphisms are equal.

Suppose now the result true at the stage \( n \). If \( k > 0 \), we have

\[
\begin{array}{l} d ^ {k} \circ \iota_ {n} = e \star d ^ {k - 1} \circ e \star \iota_ {n - 1} \circ \alpha_ {[ n - 2 ]} \\ \geq_ {n} e \star \iota_ {n} \circ e \star [ d ^ {k - 1}, 1 ] \circ \alpha_ {[ n - 2 ]} \quad (\text { induction   hypothesis   and   3.2.4.13 }) \\ = e \star \iota_ {n} \circ \alpha_ {[ n - 1 ]} \circ [ e \star d ^ {k - 1}, 1 ] \\ = \iota_ {n + 1} \circ \alpha_ {[ n - 1 ]} \circ [ d ^ {k}, 1 ] \\ \end{array}
\]

We still have to deal with the case \( k = 0 \). As \( d^0: [n] \to [n + 1] \) (resp \( [d^0, 1]: [[n - 1], 1] \to [[n], 1] \)) is equal to \( d^0 \star [n] \) (resp. \( [d^0 \star [n - 1], 1] \)), this is exactly the content of lemma 3.2.4.15.

For the second inequality, we proceed again by induction. We remark that this is true for \( n = 2 \). Suppose now the result true at the stage \( n \). We have

\[
\begin{array}{l} \left(d ^ {n + 1} \circ \iota_ {n}, d ^ {n - 1} \iota_ {n}\right) = \left(e \star d ^ {n} \circ e \star \iota_ {n - 1} \circ \alpha_ {[ n - 2 ]}, e \star d ^ {n - 2} \circ e \star \iota_ {n - 1} \circ \alpha_ {[ n - 2 ]}\right) \\ \geq_ {n - 1} e \star \iota_ {n} \circ e \star [ d ^ {n - 2}, 1 ] \circ \alpha_ {[ n - 2 ]} \quad (\text { induction   hypothesis   and   3.2.4.14 }) \\ = e \star \iota_ {n} \circ e \star \alpha_ {[ n - 1 ]} \circ [ e \star d ^ {n - 2}, 1 ] \\ = \iota_ {n + 1} \circ [ d ^ {n - 1}, 1 ] \\ \end{array}
\]

Lemma 3.2.4.18. Let \(0 < k < n\) be two integers. We denote by \(\tau^k\) the projection \([n] \to [n]^k\). We then have

\[
\tau^ {k} \circ \iota_ {n} \circ [ d ^ {k}, 1 ] \geq_ {n - 1} \tau^ {k} \circ d ^ {k} \circ \iota_ {n - 1}.
\]

Proof. We demonstrate the result by induction on \( n \). For the initialization, the only case is \( n = 2 \) and \( k = 1 \), and is obvious. Suppose now the result true at the stage \( n \), and let \( k > 1 \). We have inequalities:

\[
\begin{array}{l} \tau^ {k} \circ \iota_ {n + 1} \circ [ d ^ {k}, 1 ] = e \star \tau^ {k} \circ e \star \iota_ {n} \circ \alpha_ {[ n - 1 ]} \circ [ d ^ {k}, 1 ] \\ = e \star \tau^ {k} \circ e \star \iota_ {n} \circ e \star [ d ^ {k - 1}, 1 ] \circ \alpha_ {[ n - 2 ]} \\ \geq_ {n} e \star \tau_ {k} \circ e \star d ^ {k - 1} \circ e \star \iota_ {n - 1} \circ \alpha_ {[ n - 2 ]} \quad (\text { induction   hypothesis   and   3.2.4.13 }) \\ = \tau_ {k} \circ d ^ {k} \circ \iota_ {n} \\ \end{array}
\]

We still have to deal with the case \( k = 1 \). Using diagrams (1), (2), (4) and (5), of construction 3.2.4.2, we get a diagram:

\[
\begin{array}{l} [ [ n - 1 ], 1 ] \xrightarrow {\alpha_ {[ n - 2 ]}} e \star [ [ n - 2 ], 1 ] \xrightarrow {e \star \iota_ {n - 1}} [ n ] \\ [ d ^ {2} \otimes [ n - 2 ], 1 ] \Bigg \downarrow \qquad \qquad \qquad \Bigg \downarrow e \star [ [ n - 1 ], d ^ {0} ] \qquad \qquad \Bigg \downarrow d ^ {1} \\ [ [ 2 ] \bar {\otimes} [ n - 2 ], 1 ] \xrightarrow {e \star \pi \circ e _ {[ n - 2 ]}} e \star ([ e, 1 ] \vee [ [ n - 2 ], 1 ]) \xrightarrow {e \star \beta_ {[ n - 1 ]}} [ n + 1 ] \xrightarrow {\tau^ {1}} [ n + 1 ] ^ {1} \\ [ d ^ {1} \bar {\otimes} [ n - 2 ], 1 ] \uparrow \qquad \qquad \qquad \uparrow e \star [ [ n - 1 ], d ^ {1} ] \qquad \qquad \uparrow e \star \iota_ {n} \\ [ [ n - 1 ], 1 ] \xrightarrow {\alpha_ {[ n - 2 ]}} e \star [ [ n - 2 ], 1 ] \xrightarrow [ e \star [ d ^ {0} , 1 ] ]{} e \star [ [ n - 1 ], 1 ] \\ \end{array}
\]

where \(\pi\) is the projection \([n - 2], 2] \to [e, 1] \vee [n - 2], 1\). However, according to the diagrams (5) and (3)

132