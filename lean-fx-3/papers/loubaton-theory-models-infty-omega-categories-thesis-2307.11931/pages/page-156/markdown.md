CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Lemma 3.3.2.10. The morphism \(\{1\} \star [0] \to [1]_t \star [0]\) is an acyclic cofibration.

Proof. Using proposition 3.2.2.6 we deduce that \([1]_t \star [0]\) is the colimit of the diagram

\[
[ [ 1 ] _ {t}, 1 ] \longleftarrow [ e, 1 ] \longrightarrow [ e, 1 ] _ {t} \vee [ e, 1 ]
\]

The inclusion \(\{1\} \star [0] \to [1]_t \star [0]\) is then the composite of the following sequence

\[
\begin{array}{c} [ e, 1 ] \xrightarrow {[ d ^ {0} , 1 ]} [ [ 1 ] _ {t}, 1 ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ e, 1 ] \xrightarrow {[ e , d ^ {0} ]} [ e, 1 ] _ {t} \vee [ e, 1 ] \longrightarrow [ 1 ] _ {t} \star [ 0 ] \end{array}
\]

As the morphism \([e, d^0]\) and \([d^0, 1]\) are acyclic cofibrations, this concludes the proof.

Lemma 3.3.2.11. The morphism \(\{1\} \star [a,1] \to [1]_t \star [a,1]\) is an acyclic cofibration.

Proof. The Segal \(A\)-precategory \([1]_t \star [a, 1]\) is the colimit and the homotopy colimit of the diagram

\[
\begin{array}{c} [ 1 ] \star \emptyset \\ \Big \downarrow \\ [ 1 ] _ {t} \star \emptyset \end{array} \xrightarrow {} \begin{array}{c} [ 1 ] \star [ a, 1 ] \\ \hline \end{array} \xleftarrow {} \begin{array}{c} [ a \star [ 1 ], 1 ] \\ \Big \downarrow \\ [ a \star [ 1 ] _ {t}, 1 ] \end{array}
\]

The lemma 3.3.2.3 then implies that we have a weak equivalence from \([1]_t \star [a, 1]\) to the colimit, denoted by \(K\), of the diagram

\[
[ [ 1 ] _ {t} \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ e \star a, 1 ] \xrightarrow {[ e \star a , d ^ {1} ]} [ e, 1 ] _ {t} \vee (e \star [ a, 1 ])
\]

As all the morphisms are cofibrations, \( K \) is also the homotopy colimit of the previous diagram.

The morphism \([e,1]_t\vee (e\star [a,1])\to e\star [a,1]\) is a weak equivalence as it is a homotopy colimit of weak equivalences. Moreover, the morphism \([(1)_t\star a,1]\to [e\star a,1]\) is also a weak equivalence. This implies that the composite \(s^0\star [a,1]:[1]_t\star [a,1]\to K\to [0]\star [a,1]\) is a weak equivalence. The morphism \(\{1\} \star [a,1]\to [1]_t\star [a,1]\) is a section of \(s^0\star [a,1]\) and is then also a weak equivalence.

Lemma 3.3.2.12. The morphism \(\Lambda^1 [2]\star [0]\to [2]_t\star [0]\) is an acyclic cofibration.

Proof. The Segal \(A\)-precategory \([2]_t \star [0]\) is the colimit of the following diagram

\[
[ [ 2 ] _ {t}, 1 ] \longleftarrow [ [ 2 ], 1 ] \longrightarrow \overline {{[ 1 ] \star [ 1 ]}}
\]

146