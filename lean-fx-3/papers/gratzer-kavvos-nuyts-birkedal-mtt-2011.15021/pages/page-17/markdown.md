Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:17

\[
\boxed {\Gamma \vdash A = B \text {type} _ {\ell} @ m}
\]

\[
\frac {\mu : \operatorname{Hom} _ {\mathcal {M}} (n , m) \quad \Gamma , \Delta \operatorname{ctx} @ m \quad \Gamma \vdash \delta : \Delta @ m \quad \Delta . \widehat {\boldsymbol {\omega}} _ {\mu} \vdash A \operatorname{type} _ {\ell} @ n}{\Gamma \vdash \langle \mu | A \rangle [ \delta ] = \langle \mu | A [ \delta . \widehat {\boldsymbol {\omega}} _ {\mu} ] \rangle \operatorname{type} _ {\ell} @ m}
\]

\[
\frac {\Gamma , \Delta \operatorname{ctx} @ m \qquad \Gamma \vdash \delta : \Delta @ m \qquad \begin{array}{c} \mu : \operatorname{Hom} _ {\mathcal {M}} (n , m) \\ \Gamma . \widehat {\boldsymbol {\omega}} _ {\mu} \vdash A \operatorname{type} _ {\ell} @ n \qquad \Gamma . (\mu | \uparrow A) \vdash B \operatorname{type} _ {\ell} @ m \end{array} }{\Gamma \vdash ((\mu | A) \to B) [ \delta ] = (\mu | A [ \delta . \widehat {\boldsymbol {\omega}} _ {\mu} ]) \to B [ \delta^ {+} ] \operatorname{type} _ {\ell} @ m}
\]

\[
\frac {\Gamma \vdash A \text {type} _ {\ell} @ m}{\Gamma \vdash \Uparrow A = A \text {type} _ {\ell} @ m} \quad \frac {\ell_ {0} \leq \ell_ {1} \leq \ell_ {2} \quad \Gamma \vdash A \text {type} _ {\ell_ {0}} @ m}{\Gamma \vdash \Uparrow \Uparrow A = \Uparrow A \text {type} _ {\ell_ {2}} @ m}
\]

\[
\frac {\ell \leq \ell^ {\prime} \qquad \mu \in \operatorname{Hom} _ {\mathcal {M}} (n , m) \qquad \Gamma   \mathsf {c t x}   @   m \qquad \Gamma . \widehat {\boldsymbol {\omega}} _ {\mu} \vdash A   \mathsf {t y p e} _ {\ell}   @   n \qquad \Gamma . (\mu   |   \Uparrow A) \vdash B   \mathsf {t y p e} _ {\ell}   @   m}{\Gamma \vdash \Uparrow ((\mu   |   A) \to B) = (\mu   |   \Uparrow A) \to \Uparrow B   \mathsf {t y p e} _ {\ell^ {\prime}}   @   m}
\]

\[
\frac {\Gamma \operatorname{ctx} @ m \qquad \Gamma \vdash A \operatorname{type} _ {0} @ m}{\Gamma \vdash \operatorname{El} (\operatorname{Code} (A)) = A \operatorname{type} _ {0} @ m} \qquad \qquad \frac {\Gamma , \Delta \operatorname{ctx} @ m \qquad \Gamma \vdash \delta : \Delta @ m}{\Gamma \vdash U [ \delta ] = U \operatorname{type} _ {1} @ m}
\]

Figure 7: Equality of Types

\[
\boxed {\Gamma \vdash M = N: A @ m}
\]

\[
\frac {\mu : \operatorname{Hom} _ {\mathcal {M}} (n , m) \qquad \Gamma \vdash \delta : \Delta @ m \qquad \Delta . \widehat {\boldsymbol {\omega}} _ {\mu} \vdash A \text {type} _ {1} @ n \qquad \Gamma . \widehat {\boldsymbol {\omega}} _ {\mu} \vdash M : A [ \delta . \widehat {\boldsymbol {\omega}} _ {\mu} ] @ n}{\Gamma . \widehat {\boldsymbol {\omega}} _ {\mu} \vdash \mathbf {v} _ {0} [ (\delta . M) . \widehat {\boldsymbol {\omega}} _ {\mu} ] = M : A [ \delta . \widehat {\boldsymbol {\omega}} _ {\mu} ] @ n}
\]

\[
\frac {\Gamma \operatorname{ctx} @ m \quad \Gamma \vdash M : U @ m}{\Gamma \vdash \operatorname{Code} (\operatorname{El} (M)) = M : U @ m}
\]

\[
\nu : \operatorname{Hom} _ {\mathcal {M}} (o, n)
\]

\[
\begin{array}{c} \mu : \operatorname{Hom} _ {\mathcal {M}} (n, m) \qquad \Gamma   \mathsf {c t x} @ m \qquad \Gamma . \widehat {\boldsymbol {\omega}} _ {\mu}. \widehat {\boldsymbol {\omega}} _ {\nu} \vdash A   \mathsf {t y p e} _ {1} @ o \qquad \Gamma . \widehat {\boldsymbol {\omega}} _ {\mu}. \widehat {\boldsymbol {\omega}} _ {\nu} \vdash M _ {0}: A @ o \\ \Gamma . (\mu | \langle \nu | A \rangle) \vdash B   \mathsf {t y p e} _ {1} @ m \qquad \Gamma . (\mu \circ \nu | A) \vdash M _ {1}: B [ \uparrow . \mathsf {m o d} _ {\mu} (\mathbf {v} _ {0}) ] @ m \\ \hline \Gamma \vdash \mathsf {l e t} _ {\mu}   \mathsf {m o d} _ {\nu} (\_) \leftarrow \mathsf {m o d} _ {\nu} (M _ {0})   \text {in}   M _ {1} = M _ {1} [ \mathsf {i d}. M _ {0} ]: B [ \mathsf {i d}. \mathsf {m o d} _ {\nu} (M _ {0}) ] @ m \end{array}
\]

\[
\mu : \operatorname{Hom} _ {\mathcal {M}} (n, m)
\]

\[
\frac {\Delta , \Gamma \operatorname{ctx} @ m \qquad \Gamma \vdash \delta : \Delta @ m \qquad \Delta . \widehat {\boldsymbol {\omega}} _ {\mu} \vdash A \operatorname{type} _ {1} @ n \qquad \Delta . \widehat {\boldsymbol {\omega}} _ {\mu} \vdash M : A @ n}{\Gamma \vdash \operatorname{mod} _ {\mu} (M) [ \delta ] = \operatorname{mod} _ {\mu} (M [ \delta . \widehat {\boldsymbol {\omega}} _ {\mu} ]) : \langle \mu | A [ \delta . \widehat {\boldsymbol {\omega}} _ {\mu} ] \rangle @ m}
\]

\[
\nu : \operatorname{Hom} _ {\mathcal {M}} (o, n) \quad \mu : \operatorname{Hom} _ {\mathcal {M}} (n, m)
\]

\[
\Gamma , \Delta \operatorname{ctx} @ m \quad \Gamma \vdash \delta : \Delta @ m \quad \Delta . \widehat {\boldsymbol {\omega}} _ {\mu}. \widehat {\boldsymbol {\omega}} _ {\nu} \vdash A \text {type} _ {1} @ o \quad \Delta . \widehat {\boldsymbol {\omega}} _ {\mu} \vdash M _ {0}: \langle \nu | A \rangle @ n
\]

\[
\Delta . (\mu \mid \langle \nu \mid A \rangle) \vdash B \text {type} _ {1} @ m \quad \Delta . (\mu \circ \nu \mid A) \vdash M _ {1}: B [ \uparrow . \mathsf {m o d} _ {\mu} (\mathbf {v} _ {0}) ] @ m
\]

\[
\Gamma \vdash (\operatorname{let} _ {\mu} \operatorname{mod} _ {\nu} (\_) \leftarrow M _ {0} \text {in} M _ {1}) [ \delta ] = \operatorname{let} _ {\mu} \operatorname{mod} _ {\nu} (\_) \leftarrow M _ {0} [ \delta . \widehat {\boldsymbol {\omega}} _ {\mu} ] \text {in} M _ {1} [ \delta^ {+} ]: B [ \delta . M _ {0} [ \delta . \widehat {\boldsymbol {\omega}} _ {\mu} ] ] @ m
\]

Figure 8: Equality of Terms