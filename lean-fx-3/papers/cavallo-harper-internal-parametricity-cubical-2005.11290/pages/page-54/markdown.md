5:54

E. CAVALLO AND R. HARPER

Vol. 17:4

## APPENDIX A. FORMAL PARAMETRIC TYPE THEORY

Rules for pushing substitutions through type and term formers are omitted.

### A.1. Contexts.

\[
\begin{array}{c c c c} \text {CTX - NIL} & \text {CTX - TERM} & \text {CTX - I} & \text {CTX - RESTRICT} \\ \hline \cdot \text {ctx} & \frac {\Gamma \vdash A \text {type}}{\Gamma . A \text {ctx}} & \frac {\Gamma \text {ctx}}{\Gamma . I \text {ctx}} & \frac {\Gamma \text {ctx} \quad \Gamma \vdash r : I}{\Gamma . \backslash r \text {ctx}} \end{array}
\]

### A.2. Interval terms.

\[
\frac {\mathbf {I} \text {-VAR}}{\Gamma . \mathbf {I} \vdash \mathbf {q} _ {\mathbf {I}} : \mathbf {I}} \quad \begin{array}{c} \mathbf {I} \text {-SUBST} \\ \Delta \vdash r: \mathbf {I} \qquad \Gamma \vdash \delta : \Delta \\ \hline \Gamma \vdash r [ \delta ]: \mathbf {I} \end{array}
\]

### A.3. Interval term equality.

\[
\begin{array}{c c} \text {I - SUBST - ID} & \text {I - SUBST - CONC} \\ \Gamma \vdash r: \mathbf {I} & \Delta_ {0} \vdash r: \mathbf {I} \quad \Delta_ {1} \vdash \delta_ {0}: \Delta_ {0} \quad \Gamma \vdash \delta_ {1}: \Delta_ {1} \\ \hline \Gamma \vdash r [ \mathrm{id} ] = r: \mathbf {I} & \Gamma \vdash r [ \delta_ {0} \circ \delta_ {1} ] = r [ \delta_ {0} ] [ \delta_ {1} ]: \mathbf {I} \end{array}
\]

\[
\begin{array}{c} \text {I - SUBST - TERM} \\ \Gamma \vdash r: \mathbf {I} \qquad \Gamma . \backslash r \vdash \delta : \Delta \\ \hline \Gamma \vdash q _ {\mathbf {I}} [ \delta . r ] = r: \mathbf {I} \end{array}
\]

### A.4. Substitutions.

\[
\begin{array}{c c c} \text {SUBST - NIL} & \text {SUBST - ID} & \text {SUBST - CONC} \\ \hline \Gamma \vdash !: \cdot & \overline {{\Gamma \vdash \mathrm{id} : \Gamma}} & \frac {\Delta_ {1} \vdash \delta_ {0} : \Delta_ {0} \qquad \Gamma \vdash \delta_ {1} : \Delta_ {1}}{\Gamma \vdash \delta_ {0} \circ \delta_ {1} : \Delta_ {0}} \\ \hline \end{array} \qquad \begin{array}{c c c} \text {SUBST - TERM} \\ \frac {\Gamma \vdash \delta : \Delta \qquad \Gamma \vdash M : A [ \delta ]}{\Gamma \vdash \delta . M : \Delta . A} \end{array}
\]

\[
\begin{array}{c c c c} \text {SUBST - PROJ} & \text {SUBST - I} & \text {SUBST - RESTRICT} & \text {SUBST - FACE} \\ \frac {\Gamma \vdash A \text {type}}{\Gamma . A \vdash p : \Gamma} & \frac {\Gamma \vdash r : \mathbf {I} \qquad \Gamma . \backslash r \vdash \delta : \Delta}{\Gamma \vdash \delta . r : \Delta . \mathbf {I}} & \frac {\Gamma \vdash \delta : \Delta . \mathbf {I}}{\Gamma . \backslash q _ {\mathbf {I}} [ \delta ] \vdash \delta^ {\dagger} : \Delta} & \frac {\varepsilon \in \{0 , 1 \}}{\Gamma \vdash \varepsilon_ {\mathbf {I}} : \Gamma . \mathbf {I}} \end{array}
\]

\[
\begin{array}{c c} \text {SUBST - DEGEN} & \text {SUBST - EXCHANGE} \\ \hline \Gamma . \mathbf {I} \vdash p _ {\mathbf {I}}: \Gamma & \frac {\Gamma \text {ctx}}{\Gamma . \mathbf {I} . \mathbf {I} \vdash \mathrm{ex} _ {\mathbf {I}} : \Gamma . \mathbf {I} . \mathbf {I}} \end{array}
\]

We introduce the following abbreviations for the functorial actions of the three forms of context extension.

\[
\frac {\Gamma \vdash \delta : \Delta \qquad \Delta . \mu \vdash A \text {type}}{\Gamma . A [ \delta ] \vdash \delta^ {\times} : = (\delta \circ p) . q : \Delta . A} \qquad \qquad \frac {\Gamma \vdash \delta : \Delta}{\Gamma . I \vdash \delta^ {I} : = (\delta \circ i d ^ {\dagger}) . q _ {I} : \Delta . I}
\]

\[
\frac {\Gamma \vdash \delta : \Delta \qquad \Delta \vdash r : \mathbf {I}}{\Gamma . \backslash r [ \delta ] \vdash \delta \backslash r : = (\mathrm{id} . r \circ \delta) ^ {\dagger} : \Delta . \backslash r}
\]