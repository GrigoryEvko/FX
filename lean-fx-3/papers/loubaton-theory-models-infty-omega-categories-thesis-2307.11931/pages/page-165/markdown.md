3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

Lemma 3.3.3.9. Let n be a non null integer and a an element such that $\tau_{n}^{i}(a)=a$. The object $[2]^{2}\otimes a$ is n-relying on $d^{1}\bar{\otimes}a:e\star a\to[2]^{2}\bar{\otimes}a$.

Proof. As the morphism $d^{1}\bar{\otimes}a:e\star a\to[2]^{2}\bar{\otimes}a$ is a weak equivalence, so are the horizontal morphisms of the following diagram:

$$\begin{array}{c} [ k ] \star e \star a \xrightarrow {\sim} [ k ] \star ([ 2 ] ^ {2} \bar {\otimes} a) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \tau_ {n + k + 1} ^ {i} ([ k ] \star e \star a) \xrightarrow {\sim} \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 2 ] ^ {2} \bar {\otimes} a)) \end{array}$$

As the vertical morphisms are cofibrations, this implies that this square is homotopy cocartesian.

Lemma 3.3.3.10. Let n be a non null integer and a an element such that $\tau_{n}^{i}(a)=a$. The object $[2]\bar{\otimes}a$ is n-relying on $d^{0}\otimes a:[1]\otimes a\to[2]\bar{\otimes}a$ and $d^{2}\otimes a:e\star a\to[2]\otimes a$. Moreover, $[2]\bar{\otimes}a\coprod_{d^{0}\otimes a}\tau_{n}^{i}([1]\otimes a)$ (resp. $[2]\bar{\otimes}a\coprod_{d^{2}\bar{\otimes}a}\tau_{n}^{i}(e\star a)$) is n-relying on $d^{2}\otimes a$ (resp. $d^{0}\bar{\otimes}a$).

Proof. Consider the following diagram:

$$\begin{array}{c} [ k ] \star ([ 1 ] \otimes a) \amalg [ k ] \star ([ 1 ] \otimes a) \xrightarrow {} [ k ] \star (\Lambda^ {1} [ 2 ] \otimes a) \xrightarrow {\sim} [ k ] \star ([ 2 ] \otimes a) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \amalg \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \to \tau_ {n + k + 1} ^ {i} ([ k ] \star (\Lambda^ {1} [ 2 ] \otimes a)) \not \to \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 2 ] \otimes a)) \end{array}$$

The left square is cocartesian and so homotopy cocartesian. Horizontal morphisms of the right square are weak equivalences, so this square is also homotopy cocartesian. The outer square is then homotopy cocartesian and this implies that $[[2]\otimes a,1]$ is n-relying on $d^0\otimes a$ and $d^2\otimes a$. We then have a diagram:

$$\begin{array}{c} [ k ] \star ([ 1 ] \otimes a) \amalg [ k ] \star ([ 1 ] \otimes a) \xrightarrow {} [ k ] \star ([ 2 ] \otimes a) \xrightarrow {} [ k ] \star ([ 2 ] \bar {\otimes} a) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \amalg \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \to \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 2 ] \otimes a)) \to \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 2 ] \bar {\otimes} a)) \end{array}$$

where the two squares are homotopy cocartesian and so is the outer one. This implies the first assertion and the two others follow easily.

Lemma 3.3.3.11. Let n be an integer strictly superior to 1 and a such that $\tau_{n}^{i}(a)=a$. We consider the projection $\pi:[a,2]\to[a,1]\vee[\tau_{n-1}^{i}(a),1]$ and $\pi':[a,2]\to[\tau_{n-1}^{i}(a),1]\vee[a,1]$. We then have inequalities

$$e \star \pi \circ \epsilon_ {a} \circ [ d ^ {0} \otimes a, 1 ] \geq_ {n + 1} e \star \pi \circ \epsilon_ {a} \circ [ d ^ {1} \bar {\otimes} a, 1 ]$$

and

$$e \star \pi^ {\prime} \circ \epsilon_ {a} \circ [ d ^ {2} \bar {\otimes} a, 1 ] \geq_ {n + 1} e \star \pi \circ \epsilon_ {a} \circ [ d ^ {1} \bar {\otimes} a, 1 ].$$

155