J. Ceulemans, A. Nuyts and D. Devriese

13

In the case for \(\operatorname{suc}(v)\), we can compute that

\[
\begin{array}{l} \operatorname{suc} (v) \left[ \sigma^ {+} \right] _ {\text {aren}} ^ {\Lambda} = \operatorname{suc} (v) \left[ \operatorname{weaken} (\sigma). \mathbf {v} _ {0} ^ {1 _ {\mu}} \right] _ {\text {aren}} ^ {\Lambda} \\ = v \left[ \text { weaken } (\sigma) \right] _ {\text { aren }} ^ {\Lambda} \quad \text {(Equation (21))} \\ = \operatorname{suc} \left(v [ \sigma ] _ {\text {aren}} ^ {\Lambda}\right). \tag {Equation(17)} \\ \end{array}
\]

Repeatedly applying Lemma 5 and realising that the lifting of a regular renaming consists of the liftings of its individual atomic renamings, one can see that the statement of Lemma 5 also holds for regular renamings.

For atomic substitutions we have the following result.

▶ Lemma 6. Given an atomic substitution  \( \vdash_{sf} \sigma \)  asub( \( \hat{\Gamma} \rightarrow \hat{\Delta} \) ) @ m and a lock telescope  \( \Lambda : \text{LockTele}(m \rightarrow n) \) , we have that  \( v_{0}^{\alpha} [\sigma^{+}]_{asub}^{\Lambda} = v_{0}^{\alpha} \)  and  \( \text{suc}(v) [\sigma^{+}]_{asub}^{\Lambda} = v [\sigma]_{asub}^{\Lambda} [\pi]_{aren}^{\Lambda} \)  for every  \( \hat{\Delta} \cdot \Lambda \vdash_{sf} v \)  var @ n.

Proof. For  \( v_{0}^{\alpha} \)  the computation proceeds as follows.

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\alpha} \left[ \sigma^ {+} \right] _ {\text {asub}} ^ {\Lambda} = \mathbf {v} _ {0} ^ {\alpha} \left[ \text {weaken} (\sigma). \mathbf {v} _ {0} ^ {1 _ {\mu}} \right] _ {\text {asub}} ^ {\Lambda} \\ = \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ \mathbf {Q} _ {\hat {\Gamma}, \mu} ^ {\alpha \in \widehat {\mathbf {Q}} _ {\mu} \Rightarrow \Lambda} \right] _ {\text {aren}} (Equation(26)) \\ = \mathbf {v} _ {0} ^ {1 _ {\mu}} [ \alpha ] _ {2 - \text { cell }} ^ {\widehat {\mathbf {Q}} _ {\mu} \Rightarrow \Lambda} (Equation(19)) \\ = \mathbf {v} _ {0} ^ {(1 _ {1} * \alpha) \circ 1 _ {\mu}} (Equation(14)) \\ = \mathbf {v} _ {0} ^ {\alpha} \\ \end{array}
\]

For \(\operatorname{suc}(v)\) we have

\[
\begin{array}{l} \operatorname{suc} (v) \left[ \sigma^ {+} \right] _ {\text {asub}} ^ {\Lambda} = \operatorname{suc} (v) \left[ \text {weaken} (\sigma). \mathbf {v} _ {0} ^ {1 _ {\mu}} \right] _ {\text {asub}} ^ {\Lambda} \\ = v \left[ \text { weaken } (\sigma) \right] _ {\text { asub }} ^ {\Lambda} \tag {Equation(27)} \\ = v \left[ \sigma \right] _ {\text {asub}} ^ {\Lambda} \left[ \pi \right] _ {\text {aren}} ^ {\Lambda}. \tag {Equation(23)} \\ \end{array}
\]

#### 4.1.4 Lifted Atomic Rensubs and  \( \pi \)

▶ Lemma 7. Let \(\Phi : \mathsf{sTele}(m \to n)\) be a scoping telescope, \(\vdash_{\mathsf{sf}} \sigma \operatorname{aren}(\hat{\Gamma} \to \hat{\Delta}) @ m\) an atomic SFMTT renaming and \(\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} t \operatorname{expr} @ n\) an expression. Then \(t[\pi \cdot \Phi]_{\mathsf{aren}}[\sigma^{+} \cdot \Phi]_{\mathsf{aren}} = t[\sigma \cdot \Phi]_{\mathsf{aren}}[\pi \cdot \Phi]_{\mathsf{aren}}\).

Proof. We use Proposition 4 with the two sequences \(\bar{\sigma}\) and \(\bar{\tau}\) each consisting of the two atomic renamings on both sides of the lemma. In other words, we need to prove that \(v[\pi \cdot \Phi]_{\mathrm{aren}}[\sigma^{+}. \Phi]_{\mathrm{aren}} = v[\sigma \cdot \Phi]_{\mathrm{aren}}[\pi \cdot \Phi]_{\mathrm{aren}}\) for every variable \(\hat{\Delta} \cdot \Phi \vdash_{\mathrm{sf}} v \operatorname{var} @ n\). We will do this by induction on the number of variables in \(\Phi\).

CASE \(\Phi = \Lambda\), so \(\Phi\) contains only locks.

Now we can compute that

\[
\begin{array}{l} v [ \pi . \Lambda ] _ {\text {aren}} [ \sigma^ {+}. \Lambda ] _ {\text {aren}} = v [ \pi ] _ {\text {aren}} ^ {\Lambda} [ \sigma^ {+} ] _ {\text {aren}} ^ {\Lambda} \\ = \operatorname{suc} (v) \left[ \sigma^ {+} \right] _ {\text {aren}} ^ {\Lambda} \\ = \operatorname{suc} \left(v [ \sigma ] _ {\text {aren}} ^ {\Lambda}\right) \tag {Lemma5} \\ = v \left[ \sigma \right] _ {\text {aren}} ^ {\Lambda} \left[ \pi \right] _ {\text {aren}} ^ {\Lambda} \\ = v [ \sigma . \Lambda ] _ {\text {aren}} [ \pi . \Lambda ] _ {\text {aren}} \\ \end{array}
\]