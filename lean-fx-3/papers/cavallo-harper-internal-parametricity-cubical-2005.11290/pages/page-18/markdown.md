5:18

E. CAVALLO AND R. HARPER

Vol. 17:4

BRIDGE-FORM

\[
\frac {\Gamma , \boldsymbol {x} : \mathbf {I} \gg A \text {type} \quad \Gamma \gg M _ {0} \in A [ \mathbf {0} / \boldsymbol {x} ] \quad \Gamma \gg M _ {1} \in A [ \mathbf {1} / \boldsymbol {x} ]}{\Gamma \gg \operatorname{Bridge} _ {\boldsymbol {x} . A} (M _ {0} , M _ {1}) \text {type}}
\]

BRIDGE-INTRO

\[
\frac {\Gamma , \boldsymbol {x} : \mathbf {I} \gg M \in A}{\Gamma \gg \lambda^ {\mathbf {I}} \boldsymbol {x} . M \in \operatorname{Bridge} _ {\boldsymbol {x} . A} (M [ \mathbf {0} / \boldsymbol {x} ] , M [ \mathbf {1} / \boldsymbol {x} ])}
\]

BRIDGE-ELIM

\[
\frac {\Gamma \gg \boldsymbol {r} \in \mathbf {I} \quad \Gamma \backslash \boldsymbol {r} \gg P \in \operatorname{Bridge} _ {\boldsymbol {x} . A} (M _ {0} , M _ {1})}{\Gamma \gg P @ \boldsymbol {r} \in A [ \boldsymbol {r} / \boldsymbol {x} ]}
\]

BRIDGE-β

\[
\frac {\Gamma \gg \boldsymbol {r} \in \mathbf {I} \quad \Gamma \backslash \boldsymbol {r} , \boldsymbol {x} : \mathbf {I} \gg M \in A}{\Gamma \gg (\lambda^ {\mathbf {I}} \boldsymbol {x} . M) @ \boldsymbol {r} = M [ \boldsymbol {r} / \boldsymbol {x} ] \in A [ \boldsymbol {r} / \boldsymbol {x} ]}
\]

BRIDGE- \( \partial \)

\[
\frac {\Gamma \gg P \in \operatorname{Bridge} _ {\boldsymbol {x} . A} (M _ {0} , M _ {1}) \quad \varepsilon \in \{0 , 1 \}}{\Gamma \gg P @ \varepsilon = M _ {\varepsilon} \in A [ \varepsilon / \boldsymbol {x} ]}
\]

BRIDGE-η

\[
\frac {\Gamma \gg P \in \operatorname{Bridge} _ {\boldsymbol {x} . A} (M _ {0} , M _ {1})}{\Gamma \gg P = \lambda^ {\mathbf {I}} \boldsymbol {x} . P @ \boldsymbol {x} \in \operatorname{Bridge} _ {\boldsymbol {x} . A} (M _ {0} , M _ {1})}
\]

Figure 4: Rules for Bridge-types

EXTENT

\[
\begin{array}{l} \Gamma \gg \boldsymbol {r} \in \mathbf {I} \quad \Gamma \backslash \boldsymbol {r}, \boldsymbol {x}: \mathbf {I} \gg A \text {type} \quad \Gamma \backslash \boldsymbol {r}, \boldsymbol {x}: \mathbf {I}, a: A \gg B \text {type} \quad \Gamma \gg M \in A [ \boldsymbol {r} / \boldsymbol {x} ] \\ \Gamma \backslash \boldsymbol {r}, a _ {0}: A [ \mathbf {0} / \boldsymbol {x} ] \gg N _ {0} \in B [ \mathbf {0} / \boldsymbol {x} ] [ a _ {0} / a ] \quad \Gamma \backslash \boldsymbol {r}, a _ {1}: A [ \mathbf {1} / \boldsymbol {x} ] \gg N _ {1} \in B [ \mathbf {1} / \boldsymbol {x} ] [ a _ {1} / a ] \\ \Gamma \backslash \boldsymbol {r}, a _ {0}: A [ \mathbf {0} / \boldsymbol {x} ], a _ {1}: A [ \mathbf {1} / \boldsymbol {x} ], \overline {{a}}: \operatorname{Bridge} _ {\boldsymbol {x}. A} (a _ {0}, a _ {1}) \gg \overline {{N}} \in \operatorname{Bridge} _ {\boldsymbol {x}. B [ \overline {{a}} @ \boldsymbol {x} / a ]} (N _ {0}, N _ {1}) \\ \Gamma \gg \operatorname{extent} _ {\boldsymbol {r}} (M; a _ {0}. N _ {0}, a _ {1}. N _ {1}, a _ {0}. a _ {1}. \overline {{a}}. \overline {{N}}) \in B [ \boldsymbol {r} / \boldsymbol {x} ] [ M / a ] \\ \end{array}
\]

EXTENT- \( \partial \)

\[
\frac {\cdots \quad \varepsilon \in \{0 , 1 \} \quad \Gamma \gg M \in A [ \varepsilon / \boldsymbol {x} ]}{\Gamma \gg \operatorname{extent} _ {\varepsilon} (M ; \cdots) = N _ {\varepsilon} [ M / a _ {\varepsilon} ] \in B [ \varepsilon / \boldsymbol {x} ] [ M / a ]}
\]

EXTENT-β

\[
\frac {\cdots \quad \Gamma \backslash \boldsymbol {r} , \boldsymbol {x} : \mathbf {I} \gg M \in A}{\Gamma \gg \operatorname{extent} _ {\boldsymbol {r}} (M [ \boldsymbol {r} / \boldsymbol {x} ] ; \cdots) = \overline {{N}} [ M [ \mathbf {0} / \boldsymbol {x} ] / a _ {0} ] [ M [ \mathbf {1} / \boldsymbol {x} ] / a _ {1} ] [ \lambda^ {\mathbf {I}} \boldsymbol {x} . M / \overline {{a}} ] @ \boldsymbol {r} \in B [ \boldsymbol {r} / \boldsymbol {x} ] [ M / a ]}
\]

Figure 5: Rules for the extent operator. The elided premises in the second and third rules match those of the first rule.

cubical sets [BCH13, BCH19] is also based on an affine interval (and has been presented in a nominal style by Pitts [Pit14]). We say more about the BCH model in Section 2.5.

2.2. Bridge-types. We define Bridge-types exactly as we define Path-types: elements of  \( \text{Bridge}_{x.A}(M_0, M_1) \)  are elements of A in an abstracted bridge variable x that agree with  \( M_0 \)  and  \( M_1 \)  on their endpoints. We give rules for Bridge-types in Figure 4. The only difference is that a bridge can only be applied to a fresh variable, in keeping with the judgmental structure:  \( P@r \)  makes sense when r is apart from P.