26

A Substitution Algorithm for Multimode Type Theory: Technical Report

CASE \(\vdash_{\mathrm{ws}}\sigma \equiv^{\sigma}!\operatorname {sub}(\hat{\Gamma}\to \cdot)\) @ \(m\) (WSMTT-EQ-SUB-EMPTY-UNIQUE)

We use Proposition 12 to prove that \(\llbracket \sigma \rrbracket \approx^{\mathrm{obs}} [\llbracket !\rrbracket]\). The condition of that proposition is immediately satisfied since there are no variables in the scoping context \(\cdot, \Lambda\) for any lock telescope \(\Lambda\).

CASE \(\hat{\Gamma}.\widehat{\mathbf{B}}_{\mu}\vdash_{\mathrm{ws}}\mathbf{v}_{0}[(\sigma .t).\widehat{\mathbf{B}}_{\mu}]_{\mathrm{ws}}\equiv^{\sigma}t\exp @m\) (WSMTT-EQ-EXPR-EXTEND-VAR)

We compute (using among others the definition of  \( \llbracket\ldots\rrbracket \) )

\[
\begin{array}{l} \llbracket \mathbf {v} _ {0} [ (\sigma . t). \widehat {\boldsymbol {\Omega}} _ {\mu} ] _ {\mathrm{ws}} \rrbracket \\ = \llbracket \mathbf {v} _ {0} \rrbracket \left[ \llbracket (\sigma . t). \widehat {\boldsymbol {\Omega}} _ {\mu} \rrbracket \right] _ {\text {sub}} \\ = \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ] ^ {+}. \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \left[ (\mathrm{id} ^ {a}. [ [ t ] ]). \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {asub}} \\ = \mathbf {v} _ {0} ^ {1 _ {\mu}} [ \mathrm{id} ^ {a}. [ [ t ] ] ] _ {\text {asub}} ^ {\widehat {\boldsymbol {\Omega}} _ {\mu}} \quad (\text {Repeated application of Lemma 6}) \\ = [ [ t ] ] \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {1 _ {\mu} \in \hat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \hat {\boldsymbol {\Omega}} _ {\mu}} \right] _ {\text {aren}} \quad (\text {Equation (26)}) \\ = [ [ t ] ]. \quad (\text { Proposition   20 }) \\ \end{array}
\]

CASE \(\vdash_{\mathrm{ws}}\pi \circ (\sigma .t)\equiv^{\sigma}\sigma \operatorname {sub}(\hat{\Gamma}\to \hat{\Delta})@\mathfrak{n}\) (WSMTT-EQ-SUB-EXTEND-WEAKEN)

We have that \( ^{4} \)

\[
[ \pi \circ (\sigma . t) ] = [ \pi ] + + [ \sigma . t ] = \pi * [ \sigma ] ^ {+} * (\mathrm{id} ^ {a}. [ [ t ] ]).
\]

Since \( s[\pi]_{\mathrm{asub}} = s[\pi]_{\mathrm{aren}} \) (which is easy to prove using Proposition 11), we get that

\[
\begin{array}{l} s \left[ \llbracket \pi \circ (\sigma . t) \rrbracket \right] _ {\text {sub}} = s [ \pi ] _ {\text {asub}} \left[ \llbracket \sigma \rrbracket^ {+} \right] _ {\text {asub}} [ \mathrm{id} ^ {a}. [ [ t ] ] ] _ {\text {asub}} \\ = s \left[ [ [ \sigma ] ] \right] _ {\text {asub}} [ \pi ] _ {\text {asub}} \left[ \mathrm{id} ^ {a}. [ [ t ] ] \right] _ {\text {asub}} \tag {Lemma9} \\ \end{array}
\]

for all expressions \(s\). It therefore suffices to show that \(s'\) \([\pi]_{\mathrm{asub}}[\mathrm{id}^{\mathrm{a}}.[\![t]\!]_{\mathrm{asub}} = s'\) for every \(s'\). We do this using Proposition 11, so we take an arbitrary lock telescope \(\Lambda : \mathsf{LockTele}(n \to o)\) and variable \(\hat{\Gamma}. \Lambda \vdash_{\mathrm{sf}} v \operatorname{var} @ o\). We can then compute that

\[
\begin{array}{l} v \left[ \pi \right] _ {\text {asub}} ^ {\Lambda} \left[ \mathrm{id} ^ {a}. [ [ t ] ] \right] _ {\text {asub}} ^ {\Lambda} = v \left[ \pi \right] _ {\text {aren}} ^ {\Lambda} \left[ \mathrm{id} ^ {a}. [ [ t ] ] \right] _ {\text {asub}} ^ {\Lambda} \\ = \operatorname{suc} (v) [ \mathrm{id} ^ {a}. [ [ t ] ] ] _ {\text {asub}} ^ {\Lambda} \\ = v \left[ \mathrm{id} ^ {a} \right] _ {\text {asub}} ^ {\Lambda} = v. \quad (\text {Equations (22) and (27)}) \\ \end{array}
\]

CASE \(\vdash_{\mathrm{ws}}\sigma \equiv^{\sigma}(\pi \circ \sigma).(\mathbf{v}_{0}[\sigma .\widehat{\boldsymbol{\Omega}}_{\mu}]_{\mathrm{ws}})\operatorname {sub}(\hat{\Gamma}\to \hat{\Delta}.\mu)\) @ \(n\) (WSMTT-EQ-SUB-EXTEND-ETA)

We have that

\[
\begin{array}{l} \llbracket (\pi \circ \sigma). (\mathbf {v} _ {0} [ \sigma . \widehat {\boldsymbol {\Omega}} _ {\mu} ] _ {\mathrm{ws}}) \rrbracket = \llbracket \pi \circ \sigma \rrbracket^ {+} * (\mathrm{id} ^ {a}. \llbracket \mathbf {v} _ {0} [ \sigma . \widehat {\boldsymbol {\Omega}} _ {\mu} ] _ {\mathrm{ws}} \rrbracket) \\ = \left(\llbracket \pi \rrbracket + + \llbracket \sigma \rrbracket\right) ^ {+} * \left(\mathrm{id} ^ {a}. \llbracket \mathbf {v} _ {0} \rrbracket \left[ \llbracket \sigma . \widehat {\boldsymbol {\Omega}} _ {\mu} \rrbracket \right] _ {\text {sub}}\right) \\ = \pi^ {+} * [ [ \sigma ] ] ^ {+} * \left(\mathrm{id} ^ {a}. \mathbf {v} _ {0} ^ {1 _ {\mu}} [ [ [ \sigma ] ]. \widehat {\boldsymbol {\Omega}} _ {\mu} ] _ {\text {sub}}\right). \\ \end{array}
\]

We now use Proposition 11, so for any lock telescope \(\Lambda : \mathsf{LockTele}(n \to o)\) and variable \(\hat{\Delta} \cdot \mu \cdot \Lambda \vdash_{\mathrm{sf}} v \operatorname{var} @ o\), we need to show that

\[
v \left[ \pi^ {+} \right] _ {\text {asub}} ^ {\Lambda} \left[ [ [ \sigma ] ] ^ {+} \cdot \Lambda \right] _ {\text {sub}} \left[ \mathrm{id} ^ {a}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ]. \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} = v \left[ [ [ \sigma ] ]. \Lambda \right] _ {\text {sub}}.
\]

We distinguish two cases for \( v \).

\( ^{4} \)  Note that  \( \otimes \)  actually takes a regular substitution as left argument and an atomic substitution as right argument. We slightly abuse this notation by putting an atomic substitution to the left of the right-hand side of the following equation.