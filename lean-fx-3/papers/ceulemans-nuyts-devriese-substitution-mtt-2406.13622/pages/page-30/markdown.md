30

A Substitution Algorithm for Multimode Type Theory: Technical Report

Again we can apply the induction hypothesis because  \( (\sigma \cdot \Phi) \cdot \widehat{\mathbf{a}}_{\mu} = \sigma \cdot (\Phi \cdot \widehat{\mathbf{a}}_{\mu}) \) . The rule WSMTT-EQ-EXPR-MOD-TM-SUB is not included in Figure 4, but it is similar to WSMTT-EQ-EXPR-LAM-SUB.

▶ Lemma 29. Let  \( \vdash_{sf} \sigma \)  aren( \( \hat{\Gamma} \rightarrow \hat{\Delta} \) ) @ m be an atomic SFMTT renaming and assume that  \( \hat{\Gamma} \cdot \Lambda \vdash_{ws} \)  embed(v [ \( \sigma \cdot \Lambda \) ] \( _{aren} \) )  \( \equiv^{\sigma} \)  embed(v) [embed( \( \sigma \cdot \Lambda \) )] \( _{ws} \)  expr @ n for every lock telescope  \( \Lambda : sTele(m \rightarrow n) \)  and variable  \( \hat{\Delta} \cdot \Lambda \vdash_{sf} v \)  var @ n. Then we have that  \( \hat{\Gamma} \vdash_{ws} \)  embed(t [ \( \sigma \) ] \( _{aren} \) )  \( \equiv^{\sigma} \)  embed(t) [embed( \( \sigma \) )] \( _{ws} \)  expr @ m for all expressions  \( \hat{\Delta} \vdash_{sf} t \)  expr @ m.

Proof. By making use of Lemma 28, we have to show that \(\hat{\Gamma} \cdot \Phi \vdash_{\mathrm{ws}} \operatorname{embed}(v[\sigma \cdot \Phi]_{\mathrm{aren}}) \equiv^{\sigma} \operatorname{embed}(v)[\operatorname{embed}(\sigma \cdot \Phi)]_{\mathrm{ws}} \exp @ n\) for all \(\Phi : s\mathrm{Tele}(m \to n)\) and \(\hat{\Delta} \cdot \Phi \vdash_{\mathrm{sf}} v \operatorname{var} @ n\). We do this by induction on the number of variables in \(\Phi\).

CASE \(\Phi = \Lambda\), so \(\Phi\) has no variables

The result is exactly what we assume in this lemma.

CASE \(\Phi = \Phi^{\prime}\cdot \mu \cdot \Lambda\)

Now we distinguish between two cases for the variable \( v \).

CASE \( v = \mathbf{v}_0^\alpha \) with \( \alpha \in \mu \Rightarrow \text{locks}(\Lambda) \)

For the left-hand side, we have that

\[
\begin{array}{l} \operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha} [ \sigma . \Phi^ {\prime}. \mu . \Lambda ] _ {\text {aren}}\right) \\ = \operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha} \left[ (\sigma . \Phi^ {\prime}) ^ {+} \right] _ {\text {aren}} ^ {\Lambda}\right) \\ = \operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha}\right) \quad (\text { Lemma   5 }) \\ = \mathbf {v} _ {0} \left[ \underset {\hat {\Gamma}. \Phi^ {\prime}. \mu} {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \right] _ {\mathrm{ws}}. \quad (\text {Definition of embed} (\_)) \\ \end{array}
\]

On the other hand, we have

\[
\begin{array}{l} \operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha}\right) \left[ \operatorname{embed} \left(\sigma . \Phi^ {\prime}. \mu . \Lambda\right) \right] _ {\mathrm{ws}} \\ = \mathbf {v} _ {0} \left[ \underset {\hat {\Delta}. \Phi^ {\prime}. \mu} {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \right] _ {\mathrm{ws}} \left[ \operatorname{embed} \left(\left(\sigma . \Phi^ {\prime}\right) ^ {+}. \Lambda\right) \right] _ {\mathrm{ws}} \quad (\text {Definition of embed} (\mathbf {v} _ {0} ^ {\alpha})) \\ \equiv^ {\sigma} \mathbf {v} _ {0} \left[ \underset {\hat {\Delta}. \Phi^ {\prime}. \mu} {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \right] _ {\mathrm{ws}} \left[ (\operatorname{embed} (\sigma . \Phi^ {\prime})) ^ {+}. \Lambda \right] _ {\mathrm{ws}} \quad (\text {Lemma 27}) \\ \equiv^ {\sigma} \mathbf {v} _ {0} \left[ (\operatorname{embed} (\sigma . \Phi^ {\prime})) ^ {+}. \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\mathrm{ws}} \left[ \underset {\hat {\Gamma}. \Phi^ {\prime}. \mu} {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \right] _ {\mathrm{ws}} \quad \left(\text {WSMTT - EQ - SUB - KEY - NATURAL}\right) \\ \equiv^ {\sigma} \mathbf {v} _ {0} \left[ \underset {\hat {\Gamma}. \Phi^ {\prime}. \mu} {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \right] _ {\mathrm{ws}}. \quad (\text {WSMTT - EQ - EXPR - EXTEND - VAR}) \\ \end{array}
\]

CASE \( v = \operatorname{suc}(v') \) with \( \hat{\Delta} \cdot \Phi' \cdot \Lambda \vdash_{\mathrm{sf}} v' \operatorname{var} @ n \)

Now we see that

\[
\begin{array}{l} \operatorname{embed} \left(\operatorname{suc} \left(v ^ {\prime}\right) \left[ \sigma . \Phi^ {\prime}. \mu . \Lambda \right] _ {\text {aren}}\right) \\ = \operatorname{embed} \left(\operatorname{suc} \left(v ^ {\prime}\right) \left[ \left(\sigma . \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda}\right) \\ = \operatorname{embed} \left(\operatorname{suc} \left(v ^ {\prime} \left[ \sigma . \Phi^ {\prime} \right] _ {\text {aren}} ^ {\Lambda}\right)\right) \tag {Lemma5} \\ = \operatorname{embed} \left(v ^ {\prime} [ \sigma . \Phi^ {\prime}. \Lambda ] _ {\text {aren}}\right) [ \pi . \Lambda ] _ {\mathrm{ws}} \quad (\text {Definition of embed} (\_)) \\ \equiv^ {\sigma} \operatorname{embed} \left(v ^ {\prime}\right) \left[ \operatorname{embed} \left(\sigma . \Phi^ {\prime}. \Lambda\right) \right] _ {\mathrm{ws}} [ \pi . \Lambda ] _ {\mathrm{ws}}. \quad (\text {Induction hypothesis}) \\ \end{array}
\]