3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

Remark 3.2.1.7. The last proposition can be seen as an analogue in stratified simplicial sets of the third formula of theorem 1.2.4.14.

Proposition 3.2.1.8. The stratified Segal A-precategory $e \star [a, 2]$ is the colimit of the diagram

$$\begin{array}{c} [[2] \bar{\otimes} a, 1] \xleftarrow{[d^0 \otimes a, 1]} [e \star a, 1] \xrightarrow{[[1] \otimes a, d^1]} [e \star a, 1] \vee [a, 1] \xleftarrow{[d^0 \otimes a, 2]} [e, 1] \vee [a, 1] \xrightarrow{[a, d^1]} [e, 1] \vee [a, 2] \end{array}$$

where $[2] \bar{\otimes} a$ and $[e \star a, 1] \vee [a, 1]$ are the pushouts:

$$\begin{array}{ccc} [1] \otimes a \amalg [1] \otimes a & \xrightarrow{d^1 \otimes a \amalg d^2 \otimes a} [2] \otimes a & [[1] \otimes a, 1] \amalg [[1] \otimes a, 2] \xrightarrow{[[1] \otimes a, d^2 \amalg d^1]} [[1] \otimes a, 2] \\ \downarrow & \downarrow & \downarrow \\ e \star a \amalg e \star a & \xrightarrow{d^1 \bar{\otimes} a \amalg d^2 \bar{\otimes} a} [2] \bar{\otimes} a & [e \star a, 1] \amalg [a, 1] \longrightarrow [e \star a, 1] \vee [a, 1] \end{array}$$

Proof. The result directly follows from the construction of the functor $e \star \_ : \text{tSeg}(A) \to \text{tSeg}(A)$ and of proposition 1.2.5.19.

Proposition 3.2.1.9. The stratified Segal A-precategory $e \star e \star [a, 1]$ is the colimit of the diagram

$$\begin{array}{ccc} [[2] \bar{\otimes} a, 1] \xleftarrow{[d^0 \otimes a, 1]} [[1] \otimes a, 1] \xrightarrow{[[1] \otimes a, d^1]} [[1], 1] \vee [a, 1] \xleftarrow{[d^0 \otimes a, 2]} [e, 1] \vee [a, 1] \xrightarrow{[a, d^1]} [e, 2] \vee [a, 1] \\ [d^1 \bar{\otimes} a, 1] \uparrow & [a, d^1] \uparrow & \uparrow [a, d^2] \\ [e \star a, 1] \xleftarrow{[d^0 \star a, 1]} [a, 1] \xrightarrow{[a, d^1]} [e, 1] \vee [a, 1] \\ [d^1 \star a, 1] \downarrow & [d^0 \star a, 1] \downarrow & \downarrow [d^0 \star a, 2] \\ [[1] \star a, 1] \xleftarrow{[d^0 \star a, 1]} [e \star a, 1] \xrightarrow{[e \star a, d^1]} [e, 1] \vee [e \star a, 1] \end{array}$$

where $[2] \bar{\otimes} a$ and $[[1], 1] \vee [a, 1]$ are the pushouts:

$$\begin{array}{ccc} [1] \otimes a \amalg [1] \otimes a & \xrightarrow{d^1 \otimes a \amalg d^2 \otimes a} [2] \otimes a & [[1] \otimes a, 1] \amalg [[1] \otimes a, 2] \xrightarrow{[[1] \otimes a, d^2 \amalg d^1]} [[1] \otimes a, 2] \\ \downarrow & \downarrow & \downarrow \\ e \star a \amalg e \star a & \xrightarrow{d^1 \bar{\otimes} a \amalg d^2 \bar{\otimes} a} [2] \bar{\otimes} a & [[1], 1] \amalg [a, 1] \longrightarrow [[1], 1] \vee [a, 1] \end{array}$$

Proof. The proposition 3.2.1.8 implies that the Segal A-precategory $e \star ([e, 1] \vee [a, 1])$ is the colimit of the diagram

$$[[2] \bar{\otimes} a, 1] \xleftarrow{[d^0 \otimes a, 1]} [[1] \otimes a, 1] \xrightarrow{[[1] \otimes a, d^1]} [[1], 1] \vee [a, 1] \xleftarrow{[d^0 \otimes a, 2]} [e, 1] \vee [a, 1] \xrightarrow{[a, d^1]} [e, 2] \vee [a, 1]$$

The fact that $e \star e \star [a, 1]$ is the colimit of the given diagram then follows from the explicit expression of $e \star [\_a, 1]$ as a colimit given in proposition 3.2.1.6.

### 3.2.2 Adjunction with tPsh($\Delta$)

Construction 3.2.2.1. The (inverted) composition $g, f \mapsto g \circ f$ is a monoidal structure on the category of endomorphisms of tSeg(A). The construction 3.2.1.5 shows that $e \star \_$ is a monoid for this monoidal structure. This induces a cosimplicial object:

$$\begin{array}{rcl} \Delta & \to & \text{End}(\text{tSeg}(A)) \\ [n] & \mapsto & [n] \star \_ := \underbrace{e \star e \star \dots \star e}_{n+1} \star \_ \end{array}$$

117