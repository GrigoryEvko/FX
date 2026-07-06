3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

Proof. Consider the following diagram:

$$\begin{array}{c} [ k ] \star ([ 1 ] \otimes a) \amalg [ k ] \star ([ 1 ] \otimes a) \xrightarrow {} [ k ] \star (\Lambda^ {1} [ 2 ] \otimes a) \xrightarrow {\sim} [ k ] \star ([ 2 ] \otimes a) \\ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \amalg \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \to \tau_ {n + k + 1} ^ {i} ([ k ] \star (\Lambda^ {1} [ 2 ] \otimes a)) \xrightarrow {\sim} \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 2 ] \otimes a)) \end{array}$$

The left square is cocartesian and so homotopy cocartesian. Horizontal morphisms of the right square are weak equivalences, so this square is also homotopy cocartesian. The outer square is then homotopy cocartesian and this implies that $[ [2] \otimes a, 1 ]$ is $n$-relying on $d^0 \otimes a$ and $d^2 \otimes a$. We then have a diagram:

$$\begin{array}{c} [ k ] \star ([ 1 ] \otimes a) \amalg [ k ] \star ([ 1 ] \otimes a) \xrightarrow {} [ k ] \star ([ 2 ] \otimes a) \xrightarrow {} [ k ] \star ([ 2 ] \bar {\otimes} a) \\ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \amalg \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \to \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 2 ] \otimes a)) \to \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 2 ] \bar {\otimes} a)) \end{array}$$

where the two squares are homotopy cocartesian and so is the outer one. This implies the first assertion and the two others follow easily.

Lemma 3.2.4.11. Let $n$ be an integer strictly superior to 1 and $a$ such that $\tau_n^i(a) = a$. We consider the projection $\pi : [a, 2] \to [a, 1] \vee [\tau_{n-1}^i(a), 1]$ and $\pi' : [a, 2] \to [\tau_{n-1}^i(a), 1] \vee [a, 1]$. We then have inequalities

$$e \star \pi \circ \epsilon_ {a} \circ [ d ^ {0} \otimes a, 1 ] \geq_ {n + 1} e \star \pi \circ \epsilon_ {a} \circ [ d ^ {1} \bar {\otimes} a, 1 ]$$

and

$$e \star \pi^ {\prime} \circ \epsilon_ {a} \circ [ d ^ {2} \bar {\otimes} a, 1 ] \geq_ {n + 1} e \star \pi \circ \epsilon_ {a} \circ [ d ^ {1} \bar {\otimes} a, 1 ].$$

Proof. Using the diagram (6).3.2.4.2 we get a diagram

$$\begin{array}{c} [ e \star a, 1 ] \xrightarrow {[ d ^ {2} \bar {\otimes} a , 1 ]} [ [ 2 ] \bar {\otimes} a, 1 ] \\ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ \tau_ {n} ^ {i} (e \star a), 1 ] \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star [ a, 1 ] \xrightarrow [ e \star [ a , d ^ {0} ] ]{} e \star [ a, 2 ] \\ e \star [ \tau_ {n - 1} ^ {i} (a), 1 ] \longrightarrow e \star ([ a, 1 ] \vee [ \tau_ {n - 1} ^ {i} (a), 1 ]) \end{array}$$

The morphism $r_{e\star([a,1]\vee[\tau_{n-1}^i(a),1])}\circ e\star\pi\circ\epsilon_a$ then factors through $[ [2]\bar{\otimes}a\coprod_{d^2\bar{\otimes}a}\tau_n^i(e\star a),1]$. According to lemma 3.2.4.10, we then get the first inequalities.

For the second inequality, using the diagrams (3).3.2.4.2 and (5).3.2.4.2, we have a diagram:

$$\begin{array}{c} [ [ 1 ] \otimes a, 1 ] \xrightarrow {[ d ^ {0} \otimes a , 1 ]} [ [ 2 ] \bar {\otimes} a, 1 ] \\ [ [ 1 ] \otimes a, d ^ {1} ] \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ e \star a, 1 ] \vee [ a, 1 ] \xrightarrow {\delta_ {a}} e \star [ a, 2 ] \\ [ e \star a, d ^ {2} ] \xrightarrow {\alpha_ {a}} e \star [ a, 1 ] \xrightarrow {e \star [ a , d ^ {2} ]} e \star ([ \tau_ {n - 1} ^ {i} (a), 1 ] \vee [ a, 1 ]) \\ [ \tau_ {n} ^ {i} (e \star a), 1 ] \xrightarrow [ \alpha_ {\tau_ {n - 1} ^ {i} (a)} ]{} e \star [ \tau_ {n - 1} ^ {i} (a), 1 ] \end{array}$$

129