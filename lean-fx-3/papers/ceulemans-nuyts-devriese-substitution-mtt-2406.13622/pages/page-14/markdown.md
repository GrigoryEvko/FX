14

A Substitution Algorithm for Multimode Type Theory: Technical Report

CASE \(\Phi = \Phi^{\prime}\cdot \rho \cdot \Lambda\)

We now have to distinguish two cases for the variable \( v \).

CASE \(v = \mathbf{v}_0^\alpha\)

The computations go as follows.

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\alpha} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { aren }} \left[ \sigma^ {+}. \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { aren }} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ (\pi . \Phi^ {\prime}) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \left[ (\sigma^ {+}. \Phi^ {\prime}) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ \left(\sigma^ {+}. \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \tag {Lemma5} \\ = \mathbf {v} _ {0} ^ {\alpha} \quad (\text { Lemma   5 }) \\ \end{array}
\]

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\alpha} \left[ \sigma . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ (\sigma . \Phi^ {\prime}) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \left[ (\pi . \Phi^ {\prime}) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ (\pi . \Phi^ {\prime}) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \tag {Lemma5} \\ = \mathbf {v} _ {0} ^ {\alpha} \quad (\text { Lemma   5 }) \\ \end{array}
\]

CASE \(v = \operatorname{suc}(v')\)

Now we can compute

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \left[ \sigma^ {+}. \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ \left(\pi . \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \left[ \left(\sigma^ {+}. \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \\ = \operatorname{suc} \left(v ^ {\prime} \left[ \pi . \Phi^ {\prime} \right] _ {\text {aren}} ^ {\Lambda}\right) \left[ \left(\sigma^ {+}. \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \tag {Lemma5} \\ = \operatorname{suc} \left(v ^ {\prime} \left[ \pi . \Phi^ {\prime}. \Lambda \right] _ {\text {aren}} \left[ \sigma^ {+}. \Phi^ {\prime}. \Lambda \right] _ {\text {aren}}\right) \tag {Lemma5} \\ \end{array}
\]

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \sigma . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ \left(\sigma . \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \left[ \left(\pi . \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \\ = \operatorname{suc} \left(v ^ {\prime} \left[ \sigma . \Phi^ {\prime} \right] _ {\text {aren}} ^ {\Lambda}\right) \left[ \left(\pi . \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \tag {Lemma5} \\ = \operatorname{suc} \left(v ^ {\prime} \left[ \sigma . \Phi^ {\prime}. \Lambda \right] _ {\text {aren}} \left[ \pi . \Phi^ {\prime}. \Lambda \right] _ {\text {aren}}\right). \tag {Lemma5} \\ \end{array}
\]

Hence the result directly follows from the induction hypothesis with scoping telescope  \( \Phi^{\prime}.\Lambda \)  (which has one variable less than  \( \Phi \) ).

▶ Corollary 8. Let \(\Phi_1: \mathsf{sTele}(m \to n)\) and \(\Phi_2: \mathsf{sTele}(n \to o)\) be two scoping telescopes, \(\vdash_{\mathsf{sf}} \sigma \mathsf{asub}(\hat{\Gamma} \to \hat{\Delta}) @ m\) an atomic substitution and \(\hat{\Delta}. \Phi_1. \Phi_2 \vdash_{\mathsf{sf}} t \mathsf{expr} @ o\) an SFMTT expression. Then we have that \(t[\pi. \Phi_2]_{\mathsf{aren}}[\sigma. \Phi_1. \mu. \Phi_2]_{\mathsf{aren}} = t[\sigma. \Phi_1. \Phi_2]_{\mathsf{aren}}[\pi. \Phi_2]_{\mathsf{aren}}\).

Proof. This follows directly from Lemma 7 by taking \(\sigma\) to be \(\sigma \cdot \Phi_1\) and \(\Phi\) to be \(\Phi_2\), and realising that \(\sigma \cdot \Phi_1 \cdot \mu = (\sigma \cdot \Phi_1)^+\).

We also need a result like Lemma 7, but where \(\sigma\) is an atomic substitution instead of an atomic renaming.

▶ Lemma 9. Let \(\Phi : \mathsf{sTele}(m \to n)\) be a scoping telescope, \(\vdash_{\mathsf{sf}} \sigma \mathsf{asub}(\hat{\Gamma} \to \hat{\Delta}) @ m\) an atomic SFMTT substitution and \(\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} t \mathsf{expr} @ n\) an expression. Then \(t[\pi \cdot \Phi]_{\mathsf{aren}}[\sigma^{+} \cdot \Phi]_{\mathsf{asub}} = t[\sigma \cdot \Phi]_{\mathsf{asub}}[\pi \cdot \Phi]_{\mathsf{aren}}\).