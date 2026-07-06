Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:21

\[
\begin{array}{c} \text {GEL - FORM} \\ \Gamma \gg \boldsymbol {r} \in \mathbf {I} \qquad \Gamma \backslash \boldsymbol {r} \gg A _ {0} \text {type} \qquad \Gamma \backslash \boldsymbol {r} \gg A _ {1} \text {type} \qquad \Gamma \backslash \boldsymbol {r}, a _ {0}: A _ {0}, a _ {1}: A _ {1} \gg R \text {type} \\ \hline \Gamma \gg \operatorname{Gel} _ {\boldsymbol {r}} (A _ {0}, A _ {1}, a _ {0}. a _ {1}. R) \text {type} \end{array}
\]

\[
\begin{array}{c} \text {GEL - INTRO} \\ \Gamma \backslash \boldsymbol {r} \gg M _ {0} \in A _ {0} \qquad \Gamma \backslash \boldsymbol {r} \gg M _ {1} \in A _ {1} \qquad \Gamma \backslash \boldsymbol {r} \gg P \in R [ M _ {0}, M _ {1} / a _ {0}, a _ {1} ] \\ \hline \Gamma \gg \operatorname{gel} _ {\boldsymbol {r}} (M _ {0}, M _ {1}, P) \in \operatorname{Gel} _ {\boldsymbol {r}} (A _ {0}, A _ {1}, a _ {0}. a _ {1}. R) \end{array}
\]

\[
\begin{array}{c c} \text {GEL - FORM - \partial} \\ \varepsilon \in \{0, 1 \} \qquad \Gamma \gg A _ {\varepsilon} \text {type} \\ \hline \Gamma \gg \text {Gel} _ {\varepsilon} (A _ {0}, A _ {1}, a _ {0}. a _ {1}. R) = A _ {\varepsilon} \text {type} \end{array} \qquad \begin{array}{c c} \text {GEL - INTRO - \partial} \\ \varepsilon \in \{0, 1 \} \qquad \Gamma \gg M _ {\varepsilon} \in A _ {\varepsilon} \\ \hline \Gamma \gg \text {gel} _ {\varepsilon} (M _ {0}, M _ {1}, P) = M _ {\varepsilon} \in A _ {\varepsilon} \end{array}
\]

\[
\begin{array}{c} \text {GEL - ELIM} \\ \Gamma , \boldsymbol {x}: \mathbf {I} \gg Q \in \operatorname{Gel} _ {\boldsymbol {x}} (A _ {0}, A _ {1}, R) \\ \hline \Gamma \gg \operatorname{ungel} (\boldsymbol {x}. Q) \in R [ Q [ \mathbf {0} / \boldsymbol {x} ], Q [ \mathbf {1} / \boldsymbol {x} ] / a _ {0}, a _ {1} ] \end{array}
\]

\[
\begin{array}{c} \text {GEL- } \beta \\ \Gamma \gg P \in R [ M _ {0}, M _ {1} / a _ {0}, a _ {1} ] \\ \hline \Gamma \gg \operatorname{ungel} (\boldsymbol {x}. \operatorname{gel} _ {\boldsymbol {x}} (M _ {0}, M _ {1}, P)) = P \in R [ M _ {0}, M _ {1} / a _ {0}, a _ {1} ] \end{array}
\]

\[
\begin{array}{c} \text {GEL - } \eta \\ \Gamma \gg \boldsymbol {r} \in \mathbf {I} \qquad \Gamma \backslash \boldsymbol {r} \gg A _ {0} \text {type} \qquad \Gamma \backslash \boldsymbol {r} \gg A _ {1} \text {type} \\ \Gamma \backslash \boldsymbol {r}, a _ {0}: A _ {0}, a _ {1}: A _ {1} \gg R \text {type} \qquad \Gamma \backslash \boldsymbol {r}, \boldsymbol {x}: \mathbf {I} \gg Q \in \operatorname{Gel} _ {\boldsymbol {x}} (A _ {0}, A _ {1}, a _ {0}. a _ {1}. R) \\ \hline \Gamma \gg Q [ \boldsymbol {r} / \boldsymbol {x} ] = \operatorname{gel} _ {\boldsymbol {r}} (Q [ \mathbf {0} / \boldsymbol {x} ], Q [ \mathbf {1} / \boldsymbol {x} ], \operatorname{ungel} (\boldsymbol {x}. Q)) \in \operatorname{Gel} _ {\boldsymbol {r}} (A _ {0}, A _ {1}, a _ {0}. a _ {1}. R) \end{array}
\]

Figure 6: Rules for Gel-types.

Gel-like type can exist structurally. However, we note that in the bisimplicial set semantics of Riehl and Shulman's directed type theory [RS17], a similar setting, an issue of dimension shift does indeed prevent the existence of a universe where arrows correspond to relations [Rie18].

We now proceed to prove the relativity principle.

Theorem 2.4. For any \(A_0, A_1 \in \mathcal{U}\), \(\lambda C.\text{Bridge}_{\boldsymbol{x}, C@\boldsymbol{x}} \in \text{Bridge}_{\mathcal{U}}(A_0, A_1) \to (A_0 \times A_1 \to \mathcal{U})\) is an isomorphism.

Proof. As candidate inverse, we of course take \(\lambda R.\lambda^{\mathbf{I}}\pmb{x}.\mathsf{Gel}_{\pmb{x}}(A_{0},A_{1},R)\).

First we show that this is a left inverse, i.e., that the following holds.

\[
(R: A _ {0} \times A _ {1} \rightarrow \mathcal {U}) \rightarrow \operatorname{Path} _ {A _ {0} \times A _ {1} \rightarrow \mathcal {U}} (\operatorname{Bridge} _ {\boldsymbol {x}. \operatorname{Gel} _ {\boldsymbol {x}} (A _ {0}, A _ {1}, R)}, R)
\]

Let \( R: A_0 \times A_1 \to \mathcal{U} \) be given. We need to construct a path in \( A_0 \times A_1 \to \mathcal{U} \), so we apply function extensionality and univalence. Then for every \( a_0: A_0 \) and \( a_1: A \), we need an isomorphism \( \text{Bridge}_{\boldsymbol{x}, \text{Gel}_x(A_0, A_1, R)}(a_0, a_1) \simeq R \langle a_0, a_1 \rangle \). This isomorphism is implemented exactly by the introduction and elimination forms of the Gel-type, and the inverse conditions hold (up to exact equality) by GEL-\( \beta \) and GEL-\( \eta \).

Now we show it is also a right inverse.

\[
(C: \operatorname{Bridge} _ {\mathcal {U}} (A _ {0}, A _ {1})) \rightarrow \operatorname{Path} _ {\operatorname{Bridge} _ {\mathcal {U}} (A _ {0}, A _ {1})} (\lambda^ {\mathbf {I}} \boldsymbol {x}. \operatorname{Gel} _ {\boldsymbol {x}} (A _ {0}, A _ {1}, \operatorname{Bridge} _ {\boldsymbol {x}. C @ \boldsymbol {x}}), C)
\]