5:56

E. CAVALLO AND R. HARPER

Vol. 17:4

### A.9. Term equality.

\[
\begin{array}{c c} \text {TM - SUBST - ID} & \text {TM - SUBST - CONC} \\ \Gamma \vdash M: A & \Delta_ {0} \vdash M: A \quad \Delta_ {1} \vdash \delta_ {0}: \Delta_ {0} \quad \Gamma \vdash \delta_ {1}: \Delta_ {1} \\ \hline \Gamma \vdash M [ \mathrm{id} ] = M: A & \Gamma \vdash M [ \delta_ {0} \circ \delta_ {1} ] = M [ \delta_ {0} ] [ \delta_ {1} ]: A [ \delta_ {0} ] [ \delta_ {1} ] \end{array}
\]

\[
\begin{array}{c} \text {TM - SUBST - TERM} \\ \Gamma \vdash \delta : \Delta \qquad \Delta \vdash A \text {type} \qquad \Gamma \vdash M: A [ \delta ] \\ \hline \Gamma \vdash \mathfrak {q} [ \delta . M ] = M: A [ \delta ] \end{array}
\]

### A.10. Bridge types.

\[
\begin{array}{c c} \text {TY - BRIDGE} & \text {TM - BLAM} \\ \Gamma . \mathbf {I} \vdash A \text {type} \qquad \Gamma \vdash M _ {0}: A [ \mathbf {0} _ {\mathbf {I}} ] \qquad \Gamma \vdash M _ {1}: A [ \mathbf {1} _ {\mathbf {I}} ] & \Gamma . \mathbf {I} \vdash A \text {type} \qquad \Gamma . \mathbf {I} \vdash M: A \\ \hline \Gamma \vdash \text {Bridge} _ {A} (M _ {0}, M _ {1}) \text {type} & \overline {{\Gamma \vdash \lambda^ {\mathbf {I}} . M : \text {Bridge} _ {A} (M [ \mathbf {0} _ {\mathbf {I}} ] , M [ \mathbf {1} _ {\mathbf {I}} ])}} \end{array}
\]

\[
\begin{array}{c} \text {TM - BAPP} \\ \Gamma . \backslash r \vdash M _ {0}: A [ \mathbf {0} _ {\mathbf {I}} ] \quad \begin{array}{c} \Gamma \vdash r: \mathbf {I} \quad \Gamma . \backslash r. \mathbf {I} \vdash A \text {type} \\ \Gamma . \backslash r \vdash M _ {1}: A [ \mathbf {1} _ {\mathbf {I}} ] \quad \Gamma . \backslash r \vdash P: \operatorname{Bridge} _ {A} (M _ {0}, M _ {1}) \\ \hline \Gamma \vdash P @ r: A [ \mathrm{id}. r ] \end{array} \end{array}
\]

\[
\begin{array}{c} \text {TM - BAPP - BOUNDARY} \\ \hline \Gamma . \mathbf {I} \vdash A \text {type} \qquad \Gamma \vdash M _ {0}: A [ \mathbf {0} _ {\mathbf {I}} ] \qquad \begin{array}{c} \varepsilon \in \{0, 1 \} \\ \Gamma \vdash M _ {1}: A [ \mathbf {1} _ {\mathbf {I}} ] \qquad \Gamma \vdash P: \operatorname{Bridge} _ {A} (M _ {0}, M _ {1}) \\ \hline \Gamma \vdash P [ \varepsilon_ {\mathbf {I}} ^ {\dagger} ] @ q _ {\mathbf {I}} [ \varepsilon_ {\mathbf {I}} ] = M _ {\varepsilon}: A [ \varepsilon_ {\mathbf {I}} ] \end{array} \end{array}
\]

\[
\begin{array}{c} \text {TM - BLAM - BETA} \\ \Gamma \vdash r: \mathbf {I} \qquad \Gamma . \backslash r. \mathbf {I} \vdash A \text {type} \qquad \Gamma . \backslash r. \mathbf {I} \vdash M: A \\ \hline \Gamma \vdash \lambda . M @ r = M [ \mathrm{id}. r ]: A [ \mathrm{id}. r ] \end{array}
\]

\[
\begin{array}{c} \text {TM - BLAM - ETA} \\ \Gamma . \mathbf {I} \vdash A \text {type} \qquad \Gamma \vdash M _ {0}: A [ \mathbf {0} _ {\mathbf {I}} ] \qquad \Gamma \vdash M _ {1}: A [ \mathbf {1} _ {\mathbf {I}} ] \qquad \Gamma \vdash P: \operatorname{Bridge} _ {A} (M _ {0}, M _ {1}) \\ \hline \Gamma \vdash P = \lambda^ {\mathbf {I}}. P [ \mathrm{id} ^ {\dagger} ] @ \mathbf {q} _ {\mathbf {I}}: \operatorname{Bridge} _ {A} (M _ {0}, M _ {1}) \end{array}
\]

### A.11. Gel types.

\[
\begin{array}{c} \text {TY - GEL} \\ \Gamma \vdash r: \mathbf {I} \qquad \Gamma . \backslash r \vdash A _ {0} \text {type} \qquad \Gamma . \backslash r \vdash A _ {1} \text {type} \qquad \Gamma . \backslash r. A _ {0}. A _ {1} [ p ] \vdash R \text {type} \\ \hline \Gamma \vdash \operatorname{Gel} _ {r} (A _ {0}, A _ {1}, R) \text {type} \end{array}
\]

\[
\begin{array}{c} \text {TY - GEL - BOUNDARY} \\ \varepsilon \in \{0, 1 \} \qquad \Gamma \vdash A _ {0} \text {type} \qquad \Gamma \vdash A _ {1} \text {type} \qquad \Gamma . A _ {0}. A _ {1} [ p ] \vdash R \text {type} \\ \hline \Gamma \vdash \operatorname{Gel} _ {\varepsilon} (A _ {0} [ \varepsilon_ {\mathbf {I}} ^ {\dagger} ], A _ {1} [ \varepsilon_ {\mathbf {I}} ^ {\dagger} ], R [ \varepsilon_ {\mathbf {I}} ^ {\dagger^ {\times \times}} ]) = A _ {\varepsilon} \text {type} \end{array}
\]

\[
\begin{array}{c} \text {TM - GEL} \\ \Gamma . \backslash r \vdash M _ {1}: A _ {1} \qquad \begin{array}{c} \Gamma \vdash r: \mathbf {I} \qquad \Gamma . \backslash r \vdash M _ {0}: A _ {0} \\ \Gamma . \backslash r. A _ {0}. A _ {1} [ p ] \vdash R \text {type} \qquad \Gamma . \backslash r \vdash P: R [ \mathrm{id}. M _ {0}. M _ {1} ] \\ \hline \Gamma \vdash \operatorname{gel} _ {r} (M _ {0}, M _ {1}, P): \operatorname{Gel} _ {r} (A _ {0}, A _ {1}, R) \end{array} \end{array}
\]