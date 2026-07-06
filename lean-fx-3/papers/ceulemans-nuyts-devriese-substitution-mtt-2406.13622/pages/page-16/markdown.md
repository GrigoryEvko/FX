16

A Substitution Algorithm for Multimode Type Theory: Technical Report

Combining Lemmas 7 and 9, we get the following result.

▶ Lemma 10. Let \(\Phi : \mathsf{sTele}(m \to n)\) be a scoping telescope, \(\vdash_{\mathsf{sf}} \bar{\sigma} \operatorname{seq}(\hat{\Gamma} \to \hat{\Delta}) @ m\) a mixed sequence of atomic renamings and substitution and \(\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} t \operatorname{expr} @ n\) an SFMTT expression. Then \(t[\pi \cdot \Phi]_{\text{aren}}[\bar{\sigma}^{+} \cdot \Phi]_{\text{seq}} = t[\bar{\sigma} \cdot \Phi]_{\text{seq}}[\pi \cdot \Phi]_{\text{aren}}\).

Proof. In Figure 10 we see that the lifting and lock operations on mixed sequences of atomic rensubs consist of applying these operations to all constituent atomic rensubs. From this we deduce that also applying a general scoping telescope \(\Phi\) to such a mixed sequence amounts to applying \(\Phi\) to every constituent atomic rensub. Hence the result follows by repeatedly using Lemmas 7 and 9 for every atomic rensub in \(\bar{\sigma}\).

#### 4.1.5 Proof Technique (Part 2)

Using the results from the previous sections, we can now relax the requirement from Proposition 4 so that we only need to check the equality of applying two mixed sequences to a variable after adding a lock telescope instead of a general scoping telescope.

▶ Proposition 11. If \(\vdash_{\mathrm{sf}} \bar{\sigma}, \bar{\tau} \operatorname{seq}(\hat{\Gamma} \to \hat{\Delta}) @ m\) are two mixed sequences of SFMTT atomic rensubs such that \(v[\bar{\sigma} \cdot \Lambda]_{\mathrm{seq}} = v[\bar{\tau} \cdot \Lambda]_{\mathrm{seq}}\) for every lock telescope \(\Lambda: \operatorname{LockTele}(m \to n)\) and every variable \(\hat{\Delta} \cdot \Lambda \vdash_{\mathrm{sf}} v \operatorname{var} @ n\), then \(t[\bar{\sigma}]_{\mathrm{seq}} = t[\bar{\tau}]_{\mathrm{seq}}\) for all expressions \(\hat{\Delta} \vdash_{\mathrm{sf}} t \operatorname{expr} @ m\).

Proof. We make use of Proposition 4, so we have to show that \( v[\bar{\sigma} \cdot \Phi]_{\mathrm{seq}} = v[\bar{\tau} \cdot \Phi]_{\mathrm{seq}} \) for every scoping telescope \( \Phi : \mathsf{sTele}(m \to n) \) and every variable \( \hat{\Delta} \cdot \Phi \vdash_{\mathrm{sf}} v \operatorname{var} @ n \). We do this by induction on the number of variables in the scoping telescope \( \Phi \).

CASE \(\Phi = \Lambda\), so there are no variables in \(\Phi\).

The result is exactly the assumption of the proposition we are proving.

CASE \(\Phi = \Phi'\). \(\mu\). \(\Lambda\) with \(\Lambda\) a lock telescope

We distinguish between the two different cases for the variable v.

CASE \(v = \mathbf{v}_0^\alpha\)

For every atomic rensub \(\vdash_{\mathrm{sf}} \chi \operatorname{aren} / \operatorname{asub} (\hat{\Gamma} \to \hat{\Delta}) @ m\) we have that

\[
\mathbf {v} _ {0} ^ {\alpha} \left[ \chi . \Phi^ {\prime}. \mu . \Lambda \right] _ {\text {aren / asub}} = \mathbf {v} _ {0} ^ {\alpha} \left[ (\chi . \Phi^ {\prime}) ^ {+} \right] _ {\text {aren / asub}} ^ {\Lambda} = \mathbf {v} _ {0} ^ {\alpha}. \quad (\text {Lemmas 5 and 6})
\]

By repeatedly applying this result it follows that the same is true for sequences of atomic rensubs. In particular, we can conclude that \(\mathbf{v}_0^\alpha [\bar{\sigma} \cdot \Phi'.\mu .\Lambda ]_{\mathrm{seq}} = \mathbf{v}_0^\alpha =\) \(\mathbf{v}_0^\alpha [\bar{\tau} \cdot \Phi'.\mu .\Lambda ]_{\mathrm{seq}}\)

CASE \(v = \operatorname{suc}(v')\)

For any sequence of atomic rensubs \(\vdash_{\mathrm{sf}} \bar{\chi} \operatorname{seq}(\hat{\Gamma} \to \hat{\Delta}) @ m\) we can compute as follows

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \bar {\chi}. \Phi^ {\prime}. \mu . \Lambda \right] _ {\text { seq }} = \operatorname{suc} \left(v ^ {\prime}\right) \left[ (\bar {\chi}. \Phi^ {\prime}) ^ {+}. \Lambda \right] _ {\text { seq }} \\ = v ^ {\prime} \left[ \pi . \Lambda \right] _ {\text {aren}} \left[ (\bar {\chi}. \Phi^ {\prime}) ^ {+}. \Lambda \right] _ {\text {seq}} \\ = v ^ {\prime} \left[ \bar {\chi}. \Phi^ {\prime}. \Lambda \right] _ {\text { seq }} \left[ \pi . \Lambda \right] _ {\text { aren }} \quad (\text { Lemma   10 }) \\ \end{array}
\]

By the induction hypothesis we know that \( v' \left[ \bar{\sigma} \cdot \Phi'. \Lambda \right]_{\mathrm{seq}} = v' \left[ \bar{\tau} \cdot \Phi'. \Lambda \right]_{\mathrm{seq}} \). Hence we can conclude that

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \bar {\sigma}. \Phi^ {\prime}. \mu . \Lambda \right] _ {\text { seq }} = v ^ {\prime} \left[ \bar {\sigma}. \Phi^ {\prime}. \Lambda \right] _ {\text { seq }} \left[ \pi . \Lambda \right] _ {\text { aren }} \\ = v ^ {\prime} \left[ \bar {\tau}. \Phi^ {\prime}. \Lambda \right] _ {\text { seq }} \left[ \pi . \Lambda \right] _ {\text { aren }} \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ \bar {\tau}. \Phi^ {\prime}. \mu . \Lambda \right] _ {\text { seq }}. \\ \end{array}
\]

◀