J. Ceulemans, A. Nuyts and D. Devriese

25

CASE \(\vdash_{\mathrm{ws}}\sigma_1\circ \tau_1\equiv^{\sigma}\sigma_{2}\circ \tau_{2}\operatorname {sub}(\hat{\Gamma}\to \hat{\Xi})@m\) (WSMTT-EQ-SUB-CONG-COMPOSE)

We know from the premises that \(\vdash_{\mathrm{ws}}\sigma_1\equiv^{\sigma}\sigma_{2}\operatorname {sub}(\hat{\Delta}\to \hat{\Xi})@m\) and \(\vdash_{\mathrm{ws}}\tau_1\equiv^{\sigma}\tau_{2}\operatorname {sub}(\hat{\Gamma}\rightarrow\) \(\hat{\Delta})@m\) and hence via the induction hypothesis \([\sigma_1]\approx^{\mathrm{obs}}[\sigma_2]\) and \([\tau_1]\approx^{\mathrm{obs}}[\tau_2]\). For an arbitrary expression \(\hat{\Xi}\vdash_{\mathrm{sf}}t\exp @m\) we then have that

\[
\begin{array}{l} t \left[ \llbracket \sigma_ {1} \circ \tau_ {1} \rrbracket \right] _ {\text { sub }} = t \left[ \llbracket \sigma_ {1} \rrbracket + + \llbracket \tau_ {1} \rrbracket \right] _ {\text { sub }} \quad (\text { Definition   of } [ [ \_ ] ]) \\ = t \left[ \llbracket \sigma_ {1} \rrbracket \right] _ {\text { sub }} \left[ \llbracket \tau_ {1} \rrbracket \right] _ {\text { sub }} \\ = t \left[ \llbracket \sigma_ {2} \rrbracket \right] _ {\text { sub }} \left[ \llbracket \tau_ {1} \rrbracket \right] _ {\text { sub }} \quad (\text { Definition   of } \sigma_ {1} \approx^ {\mathrm{obs}} \sigma_ {2}) \\ = t \left[ \llbracket \sigma_ {2} \rrbracket \right] _ {\text { sub }} \left[ \llbracket \tau_ {2} \rrbracket \right] _ {\text { sub }} \quad (\text { Definition   of } \tau_ {1} \approx^ {\text { obs }} \tau_ {2}) \\ = t \left[ \llbracket \sigma_ {2} \circ \tau_ {2} \rrbracket \right] _ {\text { sub }}, \\ \end{array}
\]

which proves that \(\llbracket \sigma_1\circ \tau_1\rrbracket \approx^{\mathrm{obs}}\llbracket \sigma_2\circ \tau_2\rrbracket .\)

CASE \(\vdash_{\mathrm{ws}}\sigma_1.t_1\equiv^\sigma \sigma_2.t_2\) sub \((\hat{\Gamma}\to \hat{\Delta}.\mu)\) @ \(n\) (WSMTT-EQ-SUB-CONG-EXTEND)

The premises tell us that \(\vdash_{\mathrm{ws}}\sigma_1\equiv^\sigma \sigma_2\) sub \((\hat{\Gamma}\to \hat{\Delta})@\mathfrak{n}\) and \(\hat{\Gamma}.\widehat{\mathbf{\Omega}}_{\mu}\vdash_{\mathrm{ws}}t_{1}\equiv^{\sigma}t_{2}\exp @m\) and hence by the induction hypothesis \([\sigma_1]\approx^{\mathrm{obs}}[\sigma_2]\) and \([t_1] = [t_2]\). Lemma 15 then gives us that \([\sigma_1]^+ \approx^{\mathrm{obs}}[\sigma_2]^+\) from which it follows that

\[
\begin{array}{l} [ \sigma_ {1}. t _ {1} ] = [ \sigma_ {1} ] ^ {+} \circledast (\mathrm{id} ^ {\mathrm{a}}, [ t _ {1} ]) \quad (\text { Definition   of } [ [ \_ ] ]) \\ \approx^ {\mathrm{obs}} \llbracket \sigma_ {2} \rrbracket^ {+} \circledast (\mathrm{id} ^ {\mathrm{a}}, \llbracket t _ {1} \rrbracket) \quad \left(\llbracket \sigma_ {1} \rrbracket^ {+} \approx^ {\mathrm{obs}} \llbracket \sigma_ {2} \rrbracket^ {+}\right) \\ = \llbracket \sigma_ {2} \rrbracket^ {+} \circledast (\mathrm{id} ^ {\mathrm{a}}, \llbracket t _ {2} \rrbracket) \\ = \llbracket \sigma_ {2}. t _ {2} \rrbracket . \\ \end{array}
\]

CASE \(\vdash_{\mathrm{ws}}\sigma_1.\widehat{\mathbf{\Omega}}_\mu \equiv^\sigma \sigma_2.\widehat{\mathbf{\Omega}}_\mu \operatorname {sub}(\hat{\Gamma}.\widehat{\mathbf{\Omega}}_\mu \to \hat{\Delta}.\widehat{\mathbf{\Omega}}_\mu)\) @ \(m\) (WSMTT-EQ-SUB-CONG-LOCK)

From the premise we know that \(\vdash_{\mathrm{ws}}\sigma_1\equiv^\sigma \sigma_2\) sub \((\hat{\Gamma}\to \hat{\Delta})@\mathfrak{n}\) and hence via induction \([\sigma_1]\approx^{\mathrm{obs}}[\sigma_2]\). We can then use Lemma 14 to see that \([\sigma_1.\widehat{\mathbf{\Omega}}_\mu ] = [\sigma_1].\widehat{\mathbf{\Omega}}_\mu\) is observationally equivalent to \([\sigma_2.\widehat{\mathbf{\Omega}}_\mu ] = [\sigma_2].\widehat{\mathbf{\Omega}}_\mu\).

CASE \(\hat{\Gamma} \vdash_{\mathrm{ws}} (\lambda^{\mu}(t)) [\sigma]_{\mathrm{ws}} \equiv^{\sigma} \lambda^{\mu}(t [\sigma^{+}]_{\mathrm{ws}}) \exp @ n\) (WSMTT-EQ-EXPR-LAM-SUB)

Since all atomic SFMTT substitutions can be pushed through \(\lambda^{\mu}(\_)\) (see Equation (9)) and the lifting of a regular substitution consists of the lifted atomic substitutions, we have (also making use of the definition of \([\_]\))

\[
\llbracket (\lambda^ {\mu} (t)) [ \sigma ] _ {\mathrm{ws}} \rrbracket = \llbracket \lambda^ {\mu} (t) \rrbracket [ [ \sigma ] ] _ {\mathrm{sub}} = \lambda^ {\mu} ([ [ t ] ]) [ [ \sigma ] ] _ {\mathrm{sub}} = \lambda^ {\mu} ([ [ t ] ] [ [ \sigma ] ] ^ {+} ] _ {\mathrm{sub}}).
\]

On the other hand we know that \(\llbracket \lambda^{\mu}(t[\sigma^{+}]_{\mathrm{ws}})\rrbracket = \lambda^{\mu}([t][[\sigma^{+}]]_{\mathrm{sub}})\). We conclude that both expressions are indeed equal because \(\llbracket \sigma^{+}\rrbracket \approx^{\mathrm{obs}}[\sigma]^{+}\) by Lemma 17.

CASE \(\hat{\Gamma} \vdash_{\mathrm{ws}} (\mathsf{app}_{\mu}(f; t)) [\sigma]_{\mathrm{ws}} \equiv^{\sigma} \mathsf{app}_{\mu}(f[\sigma]_{\mathrm{ws}}; t[\sigma. \widehat{\mathbf{\Omega}}_{\mu}]_{\mathrm{ws}}) \exp @ n\) (WSMTT-EQ-EXPR-APP-SUB)

We have

\[
\begin{array}{l} \llbracket \left(\mathsf {a p p} _ {\mu} (f; t)\right) [ \sigma ] _ {\mathrm{ws}} \rrbracket \\ = \left(\mathsf {a p p} _ {\mu} ([ [ f ] ]; [ [ t ] ])\right) [ [ \sigma ] ] _ {\text {sub}} \quad \text {(Definition of} [ [ \_ ] ]) \\ = \mathsf {a p p} _ {\mu} ([ [ f ] ] [ [ \sigma ] ] _ {\text {sub}}; [ [ t ] ] [ [ \sigma ] ]. \widehat {\boldsymbol {\Omega}} ] _ {\text {sub}}) \quad (\text {Repeated use of Equation (10)}) \\ \end{array}
\]

and

\[
\llbracket \mathsf {a p p} _ {\mu} \left(f [ \sigma ] _ {\mathrm{ws}}; t [ \sigma . \widehat {\boldsymbol {\Omega}} _ {\mu} ] _ {\mathrm{ws}}\right) \rrbracket = \mathsf {a p p} _ {\mu} \left(\llbracket f \rrbracket [ [ \sigma ] ] _ {\mathrm{sub}}; \llbracket t \rrbracket [ [ \sigma . \widehat {\boldsymbol {\Omega}} _ {\mu} ] ] _ {\mathrm{sub}}\right).
\]

The result follows immediately since \(\llbracket \sigma .\widehat{\mathbf{\Omega}}_{\mu}\rrbracket = \llbracket \sigma \rrbracket .\widehat{\mathbf{\Omega}}_{\mu}\).

The cases for pushing substitutions through all other expression constructors are proved similarly.