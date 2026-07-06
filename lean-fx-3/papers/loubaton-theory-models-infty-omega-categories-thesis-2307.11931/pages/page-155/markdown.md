3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

Consider now the span

$$e \star [ a , 1 ] \xleftarrow {(3 . 3 . 2 . 5)} [ [ 2 ] ^ { 2 } \bar { \otimes } a , 1 ] \coprod _ { [ [ 1 ] _ { t } \otimes a , 1 ] } [ [ 1 ] _ { t } , 1 ] \vee [ a , 1 ] \rightarrow ( \overline { { [ 1 ] \star [ a , 1 ] } } ) _ { \mathrm { m k } } \tag {3.3.2.7}$$

As the right hand morphism is a cofibration, and as (3.3.2.5) is a weak equivalence, the canonical morphism from $$(\overline{[1] \star [a, 1]})_{\mathrm{mk}}$$ to the colimit of (3.3.2.7) is a weak equivalence. Using the diagram (3.3.2.4), the colimit of (3.3.2.7) is also the colimit of the following diagram

$$\begin{array} { c } { { e \star [ a , 1 ] \xleftarrow {} [ e , 1 ] \vee [ a , 1 ] \xrightarrow { [ a , d ^ { 1 } ] } [ e , 2 ] \vee [ a , 1 ] } } \\ { { \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad [ a , d ^ { 2 } ] } } \\ { { [ e \star a , 1 ] \xleftarrow { [ d ^ { 0 } \star a , 1 ] } [ a , 1 ] \xrightarrow { [ a , d ^ { 1 } ] } [ e , 1 ] \vee [ a , 1 ] } } } \\ { { [ d ^ { 1 } \star a , 1 ] \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad [ d ^ { 0 } \star a , 2 ] } } } \\ { { [ [ 1 ] \star a , 1 ] \xleftarrow { [ d ^ { 0 } \star a , 1 ] } [ e \star a , 1 ] \xrightarrow { [ e \star a , d ^ { 1 } ] } [ e , 1 ] \vee [ e \star a , 1 ] } } } \end{array}$$

As the upper left square is cocartesian, the colimit of the previous diagram is equivalent to the colimit of the given diagram. All put together, we have demonstrated the assertion.

□

### Lemma 3.3.2.8. The morphism

$$[ e , 1 ] \vee ( e \star [ a , 1 ] ) \cup \{ 1 \} \star [ e \star a , 1 ] \rightarrow [ e , 1 ] \vee ( e \star [ e \star a , 1 ] )$$

is a weak equivalence.

Proof. We have a cocartesian square

$$\begin{array} { c } { { [ e , 1 ] \cup e \star [ a , 1 ] \xrightarrow { [ e , 1 ] \cup e \star [ d ^ { 0 } \star a , 1 ] } [ e , 1 ] \cup e \star [ e \star a , 1 ] } } \\ { { \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad [ e , 1 ] \vee ( e \star [ a , 1 ] ) \longrightarrow [ e , 1 ] \vee ( e \star [ a , 1 ] ) \cup \{ 1 \} \star [ e \star a , 1 ] } } \end{array} \tag {3.3.2.9}$$

Remark that the left vertical morphism is the vertical colimit and homotopy colimit of the diagram

$$\begin{array} { c } { { [ e , 1 ] \cup [ e \star a , 1 ] \xleftarrow {} [ e , 1 ] \cup [ a , 1 ] \longrightarrow [ e , 1 ] \cup [ e , 1 ] \vee [ a , 1 ] } } \\ { { \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad [ e , 1 ] \vee [ e \star a , 1 ] \xleftarrow {} [ e , 1 ] \vee [ a , 1 ] \longrightarrow [ e , 2 ] \vee [ a , 1 ] } } \end{array}$$

and is then a weak equivalence. Similarly, $$[ e , 1 ] \cup e \star [ e \star a , 1 ] \rightarrow [ e , 1 ] \vee ( e \star [ e \star a , 1 ] )$$ is a weak equivalence. This implies that the right vertical morphism of (3.3.2.9) is a weak equivalence. By two out of three this concludes the proof.

145