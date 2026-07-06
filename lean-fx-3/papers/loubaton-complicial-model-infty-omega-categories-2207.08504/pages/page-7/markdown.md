CONTENTS

op-cone, denoted by \(\_ \star 1\), \(1 \stackrel{\infty}{\star}\) and \(1 \star\) , that send an \((0,\omega)\)-category \(C\) onto the following pushouts:

![img-1.jpeg](img-1.jpeg)

![img-2.jpeg](img-2.jpeg)

![img-3.jpeg](img-3.jpeg)

We also present a formula that illustrates the interaction between the suspension and the Gray cylinder. As this formula plays a crucial role in this text, we provide its intuition at this stage.

If \( A \) is any \( (0, \omega) \)-category, the suspension of \( A \), denoted by \( [A, 1] \), is the \( (0, \omega) \)-category having two objects - denoted by 0 and 1- and such that

\[
\operatorname{Hom} _ {[ A, 1 ]} (0, 1) := A, \quad \operatorname{Hom} _ {[ A, 1 ]} (1, 0) := \emptyset , \quad \operatorname{Hom} _ {[ A, 1 ]} (0, 0) = \operatorname{Hom} _ {[ A, 1 ]} (1, 1) := \{i d \}.
\]

We also define \([1] \vee [A, 1]\) as the gluing of \([1]\) and \([A, 1]\) along the 0-target of \([1]\) and the 0-source of \([A, 1]\). We define similarly \([A, 1] \vee [1]\). These two objects come along with whiskerings:

\[
\nabla : [ A, 1 ] \to [ 1 ] \vee [ A, 1 ] \quad \text { and } \quad \nabla : [ A, 1 ] \to [ A, 1 ] \vee [ 1 ]
\]

that preserve the extremal points.

The \((0,\omega)\)-category \([1]\otimes [1]\) is induced by the diagram:

![img-4.jpeg](img-4.jpeg)

and is then equal to the colimit of the following diagram:

\[
[ 1 ] \vee [ 1 ] \xleftarrow {\nabla} [ 1 ] \hookrightarrow [ [ 1 ], 1 ] \leftarrow [ 1 ] \xrightarrow {\nabla} [ 1 ] \vee [ 1 ].
\]

The \((0,\omega)\)-category \([1],1]\otimes [1]\) is induced by the diagram:

![img-5.jpeg](img-5.jpeg)

and is then equal to the colimit of the following diagram:

\[
[ 1 ] \vee [ [ 1 ], 1 ] \xleftarrow {\nabla} [ [ 1 ] \otimes \{0 \}, 1 ] \hookrightarrow [ [ 1 ] \otimes [ 1 ], 1 ] \leftarrow [ [ 1 ] \otimes \{1 \}, 1 ] \xrightarrow {\nabla} [ [ 1 ], 1 ] \vee [ 1 ]
\]

We prove a formula that combines these two examples:

Theorem 1.2.4.13. In the category of \((0,\omega)\)-categories, there exists an isomorphism, natural in \(A\), between \([A,1]\otimes [1]\) and the colimit of the following diagram

\[
[ 1 ] \vee [ A, 1 ] \xleftarrow {\nabla} [ A \otimes \{0 \}, 1 ] \longrightarrow [ A \otimes [ 1 ], 1 ] \longleftarrow [ A \otimes \{1 \}, 1 ] \xrightarrow {\nabla} [ A, 1 ] \vee [ 1 ]
\]

We also provide similar formulas for the Gray cone, the Gray o-cone and the Gray op-cone.

7