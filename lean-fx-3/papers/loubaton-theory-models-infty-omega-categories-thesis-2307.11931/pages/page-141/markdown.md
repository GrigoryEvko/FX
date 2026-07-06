3.2. GRAY CONSTRUCTIONS FOR STRATIFIED SEGAL A-CATEGORIES

where \([2] \bar{\otimes} a\) and \([(1), 1] \vee [a, 1]\) are the pushouts:

\[
\begin{array}{c} [ 1 ] \otimes a \amalg [ 1 ] \otimes a \xrightarrow {d ^ {1} \otimes a \amalg d ^ {2} \otimes a} [ 2 ] \otimes a \\ \Big \downarrow \\ e \star a \amalg e \star a \xrightarrow [ d ^ {1} \bar {\otimes} a \amalg d ^ {2} \bar {\otimes} a ]{} [ 2 ] \bar {\otimes} a \end{array}
\]

\[
\begin{array}{c} [ [ 1 ] \otimes a, 1 ] \amalg [ [ 1 ] \otimes a, 2 ] \xrightarrow {[ [ 1 ] \otimes a , d ^ {2} \amalg d ^ {1} ]} [ [ 1 ] \otimes a, 2 ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ [ 1 ], 1 ] \amalg [ a, 1 ] \xrightarrow {} [ [ 1 ], 1 ] \vee [ a, 1 ] \end{array}
\]

Proof. Let's start by studying the object \( H(a,2) \). Here is a final subcategory of \( \Delta_{/[2]}^2 \):

\[
\begin{array}{c} [ 1 ] ^ {o p} \star [ 0 ] \xrightarrow {d ^ {2}} [ 1 ] ^ {o p} \star [ 1 ] \xleftarrow {d ^ {1}} [ 0 ] ^ {o p} \star [ 1 ] \\ d ^ {2} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ 2 ] ^ {o p} \star [ 0 ] \xrightarrow [ s ^ {2} ]{} [ 2 ] \xleftarrow [ s ^ {0} ]{} [ 0 ] ^ {o p} \star [ 2 ] \end{array}
\]

The Segal \(A\)-precategory \(H(a,2)\) is then the colimit of the following diagram:

\[
[ [ 2 ] \otimes a, 1 ] \stackrel {[ d ^ {0} \otimes a, 1 ]} {\longleftrightarrow} [ [ 1 ] \otimes a, 1 ] \stackrel {[ [ 1 ] \otimes a, d ^ {1} ]} {\longrightarrow} [ [ 1 ] \otimes a, 1 ] \vee [ a, 1 ] \stackrel {[ d ^ {0} \otimes a, 2 ]} {\longleftrightarrow} [ a, 2 ] \stackrel {[ a, d ^ {1} ]} {\longrightarrow} [ a, 3 ]
\]

The Segal \(A\)-precategory \(e \star ([e, 1] \vee [a, 1])\) is then the colimit of the following diagram:

\[
[ [ 2 ] \bar {\otimes} a, 1 ] \stackrel {[ d ^ {0} \otimes a, 1 ]} {\longleftrightarrow} [ [ 1 ] \otimes a, 1 ] \stackrel {[ [ 1 ] \otimes a, d ^ {1} ]} {\longrightarrow} [ [ 1 ], 1 ] \vee [ a, 1 ] \stackrel {[ d ^ {0} \otimes a, 2 ]} {\longleftrightarrow} [ e, 1 ] \vee [ a, 1 ] \stackrel {[ a, d ^ {1} ]} {\longrightarrow} [ e, 2 ] \vee [ a, 1 ]
\]

The fact that \([1] \star [a, 1]\) is the colimit of the given diagram then follows from the equality \([1] \star [a, 1] = e \star (e \star [a, 1])\) and from the explicit expression of \(e \star [a, 1]\) given in proposition 3.2.2.6.

#### 3.2.3 Link between the Gray cylinder and Gray cone

3.2.3.1. There is a canonical morphism \( I \otimes [a, n] \to e \star [a, n] \) sending \( [a, n_0] \vee [[n_1] \otimes a, 1] \vee [a, n_2] \) to \( [[n_1] \otimes a, 1] \vee [a, n_2] \). Note that the induced morphism \( I \otimes [e, 1] \to e \star [e, 1] \to e \star [e, 1]_t \) factors through \( I \otimes [e, 1]_t \). We can then extend it by colimit to a natural transformation \( I \otimes C \to e \star C \).

We now define \((I\otimes [a,n])_{/\{0\} \otimes [a,n]}\) and \([a,n_0]\vee [[n_1]\otimes a,1]\vee [a,n_2]_{/[a,n_0]}\) as the pushouts:

\[
\begin{array}{c} [ a, n ] \otimes \{0 \} \longrightarrow I \otimes [ a, n ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \longrightarrow (I \otimes [ a, n ]) _ {/ \{0 \} \otimes [ a, n ]} \end{array}
\]

\[
\begin{array}{c} [ a, n _ {0} ] \longrightarrow [ a, n _ {0} ] \vee [ [ n _ {1} ] \otimes a, 1 ] \vee [ a, n _ {2} ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \longrightarrow [ a, n _ {0} ] \vee [ [ n _ {1} ] \otimes a, 1 ] \vee [ a, n _ {2} ] _ {/ [ a, n _ {0} ]} \end{array}
\]

By Segal extensions and by two out of three, the following canonical morphism

\[
[ a, n _ {0} ] \vee [ [ n _ {1} ] \otimes a, 1 ] \vee [ a, n _ {2} ] _ {/ [ a, n _ {0} ]} \rightarrow [ [ n _ {1} ] \otimes a, 1 ] \vee [ a, n _ {2} ]
\]

131