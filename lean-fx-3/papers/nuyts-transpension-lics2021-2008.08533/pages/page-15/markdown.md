Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:15

WDRA

\[
\begin{array}{l} \mu : p \to q \\ \frac {p \mid \Gamma , \widehat {\mathbf {u}} _ {\mu} \vdash A \text {type} _ {\ell}}{q \mid \Gamma \vdash \langle \mu \mid A \rangle \text {type} _ {\ell}} \end{array}
\]

WDRA:ELIM

\[
\mu : p \to q \quad \nu : q \to r
\]

\[
q \mid \Gamma , \widehat {\mathbf {u}} _ {\nu} \vdash \hat {a}: \langle \mu \mid A \rangle
\]

\[
r \mid \Gamma , \nu \mid \hat {x}: \langle \mu \mid A \rangle \vdash C \text {type}
\]

WDRA:INTRO

\[
\begin{array}{l} \mu : p \to q \\ \frac {p \mid \Gamma , \widehat {\mathbf {u}} _ {\mu} \vdash a : A}{q \mid \Gamma \vdash \mathsf {m o d} _ {\mu} a : \langle \mu \mid A \rangle} \end{array}
\]

\[
r \mid \Gamma , \nu \circ \mu \mid x: A \vdash c: C [ \mathsf {m o d} _ {\mu} x / \hat {x} ]
\]

\[
r \mid \Gamma \vdash \operatorname{let} _ {\nu} (\operatorname{mod} _ {\mu} x = \hat {a}) \text {in} c: C [ \hat {a} / \hat {x} ]
\]

\[
\text { where } \operatorname{let} _ {\nu} (\operatorname{mod} _ {\mu} x = \operatorname{mod} _ {\mu} a) \text { in } c = c [ a / x ]
\]

Figure 4: Typing rules for MTT's modal types (weak DRAs) [GKNB21][Nuy20a, fig. 5.6].

can make a point about de Bruijn indices. Although variables in Fig. 3 are named, the rules CTX-EXT:WKN and CTX-EXT:VAR effectively enforce a de Bruijn discipline, where we can only name the last variable in the context and have to weaken explicitly if it is deeper down, e.g.

\[
x: A, y: B, z: C \vdash x [ (y / \emptyset) ] [ (z / \emptyset) ]: A [ (x / \emptyset) ] [ (y / \emptyset) ] [ (z / \emptyset) ].
\]

We take the viewpoint \( ^{8} \) that the official system is unnamed and uses this substitution-based de Bruijn discipline to refer to variables. In order to improve human communication, we will name variables anyway and use the resulting redundancy to leave weakening substitutions implicit unambiguously. This allows for the following unofficial admissible ‘rule’

CTX-EXT:VAR:LOOKUP

\[
\frac {q \mid \Gamma , x : T , \Delta \mathsf {c t x}}{q \mid \Gamma , x : T , \Delta \vdash x : T}.
\]

Furthermore, we use other common notational conventions such as writing \((t / x)\) instead of \((\mathrm{id}_{\Gamma}, t / x): \Gamma \to (\Gamma, x: T)\).

We assume that DTT has a universe à la Coquand with mutually inverse encoding and decoding operations (which we will henceforth suppress), and we ignore cumulativity-related hassle, referring to Gratzer et al. [GKNB21] for details.

3.3.2. Modal types, part 1. Before proceeding to the MTT-specific structural rules, let us first have a look at the formation and introduction rules WDRA and WDRA:INTRO of modal types \(\langle \mu |A\rangle\) in Fig. 4. These are not unlike the formation and introduction rules of the transpension type in Fig. 1 and work by transposition: we apply the left adjoint of the modality \(\mu\) (in the form of a lock) to the premise's context. As such, they behave like DRAs, but their elimination rule WDRA:ELIM (which we consider later) is weaker, so we call them weak DRAs.

3.3.3. Structural rules. The structural rules of MTT are listed in Fig. 5. Context formation starts with the empty context which exists at any mode, and proceeds by adding locks and variables.

\( ^{8} \) as is done in the MTT technical report [GKNB20a]; the paper [GKNB21] speaks from a more implementation-oriented perspective.