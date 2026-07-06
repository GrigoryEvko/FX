Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:55

### A.5. Substitution equality.

SUBST-NIL-ETA

\[
\frac {\Gamma \vdash \delta : \cdot}{\Gamma \vdash \delta = ! : \cdot}
\]

SUBST-ID-CONC

\[
\overline {{\Gamma \vdash \mathrm{id} \circ \delta = \delta : \Delta}}
\]

SUBST-CONC-ID

\[
\overline {{\Gamma \vdash \delta \circ \mathrm{id} = \delta : \Delta}}
\]

SUBST-CONC-CONC

\[
\frac {\Delta_ {1} \vdash \delta_ {0} : \Delta_ {0} \qquad \Delta_ {2} \vdash \delta_ {1} : \Delta_ {1} \qquad \Gamma \vdash \delta_ {2} : \Delta_ {2}}{\Gamma \vdash (\delta_ {0} \circ \delta_ {1}) \circ \delta_ {2} = \delta_ {0} \circ (\delta_ {1} \circ \delta_ {2}) : \Delta_ {0}}
\]

SUBST-PROJ-TERM

\[
\frac {\Gamma \vdash \delta : \Delta \qquad \Delta \vdash A \text {type} \qquad \Gamma \vdash M : A}{\Gamma \vdash p \circ (\delta . M) = \delta : \Delta}
\]

SUBST-TERM-ETA

\[
\frac {\Delta \vdash A \text {type} \quad \Gamma \vdash \delta : \Delta . A}{\Gamma \vdash \delta = (\mathfrak {p} \circ \delta) . \mathfrak {q} [ \delta ] : \Delta . A}
\]

SUBST-EQ-I

\[
\frac {\Delta \text {ctx} \quad \Gamma \vdash \delta : \Delta . \mathbf {I}}{\Gamma \vdash \delta = \delta^ {\dagger} . \mathbf {q _ {I}} [ \delta ] : \Delta . \mathbf {I}}
\]

SUBST-EQ-RESTRICT

\[
\frac {\Gamma \vdash \boldsymbol {r} : \mathbf {I} \qquad \Gamma . \backslash \boldsymbol {r} \vdash \delta : \Delta}{\Gamma . \backslash \boldsymbol {r} \vdash \delta = (\delta . \boldsymbol {r}) ^ {\dagger} : \Delta}
\]

SUBST-I-NATURAL

\[
\frac {\Gamma \vdash \delta : \Delta \qquad \Xi \vdash \boldsymbol {r} : \mathbf {I} \qquad \Xi . \backslash \boldsymbol {r} \vdash \gamma : \Gamma}{\Xi \vdash (\delta \circ \gamma) . \boldsymbol {r} = \delta^ {\mathbf {I}} \circ (\gamma . \boldsymbol {r}) : \Delta . \mathbf {I}}
\]

SUBST-RESTRICT-NATURAL

\[
\frac {\Gamma \vdash \delta : \Delta . \mathbf {I} \qquad \Xi \vdash \gamma : \Gamma}{\Xi . \backslash \mathbf {q _ {I}} [ \delta \circ \gamma ] \vdash (\delta \circ \gamma) ^ {\dagger} = \delta^ {\dagger} \circ (\gamma \backslash \mathbf {q _ {I}} [ \delta ]) : \Delta}
\]

SUBST-FACE-NATURAL

\[
\frac {\varepsilon \in \{0 , 1 \} \qquad \Gamma \vdash \delta : \Delta}{\Gamma \vdash \delta^ {\mathbf {I}} \circ \varepsilon_ {\mathbf {I}} = \varepsilon_ {\mathbf {I}} \circ \delta : \Delta . \mathbf {I}}
\]

SUBST-DEGEN-NATURAL

\[
\frac {\Gamma \vdash \delta : \Delta}{\Gamma . \mathbf {I} \vdash \delta \circ p _ {\mathbf {I}} = p _ {\mathbf {I}} \circ \delta^ {\mathbf {I}} : \Delta}
\]

SUBST-EXCHANGE-NATURAL

\[
\frac {\Gamma \vdash \delta : \Delta}{\Gamma . \mathbf {I} . \mathbf {I} \vdash \delta^ {\mathbf {I I}} \circ \mathrm{ex} _ {\mathbf {I}} = \mathrm{ex} _ {\mathbf {I}} \circ \delta^ {\mathbf {I I}} : \Delta . \mathbf {I} . \mathbf {I}}
\]

SUBST-PROJ-FACE

\[
\frac {\varepsilon \in \{0 , 1 \}}{\Gamma \vdash p _ {\mathbf {I}} \circ \varepsilon_ {\mathbf {I}} = \mathrm{id} : \Gamma}
\]

SUBST-PROJ-EXCHANGE

\[
\overline {{\Gamma . \mathbf {I} . \mathbf {I} \vdash p _ {\mathbf {I}} \circ e x _ {\mathbf {I}} = p _ {\mathbf {I}} ^ {\mathbf {I}} : \Gamma . \mathbf {I}}}
\]

SUBST-EXCHANGE-EXCHANGE

\[
\overline {{\Gamma . \mathbf {I} . \mathbf {I} \vdash \mathrm{ex} _ {\mathbf {I}} \circ \mathrm{ex} _ {\mathbf {I}} = \mathrm{id} : \Gamma . \mathbf {I} . \mathbf {I}}}
\]

### A.6. Types.

TY-SUBST

\[
\frac {\Delta \vdash A \text {type} \qquad \Gamma \vdash \delta : \Delta}{\Gamma \vdash A [ \delta ] \text {type}}
\]

### A.7. Type equality.

TY-SUBST-ID

\[
\overline {{\Gamma \vdash A [ \mathrm{id} ] = A \text {type}}}
\]

TY-SUBST-CONC

\[
\frac {\Delta_ {0} \vdash A \text {type} \qquad \Delta_ {1} \vdash \delta_ {0} : \Delta_ {0} \qquad \Gamma \vdash \delta_ {1} : \Delta_ {1}}{\Gamma \vdash A [ \delta_ {0} \circ \delta_ {1} ] = A [ \delta_ {0} ] [ \delta_ {1} ] \text {type}}
\]

### A.8. Terms.

TM-VAR

\[
\frac {\Gamma \vdash A \text {type}}{\Gamma . A \vdash \mathfrak {q} : A [ \mathfrak {p} ]}
\]

TM-SUBST

\[
\frac {\Gamma \vdash \delta : \Delta \qquad \Delta \vdash M : A}{\Gamma \vdash M [ \delta ] : A [ \delta ]}
\]