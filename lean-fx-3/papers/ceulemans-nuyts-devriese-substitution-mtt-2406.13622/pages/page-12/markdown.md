12

A Substitution Algorithm for Multimode Type Theory: Technical Report

|  SF-MIX-ID | SF-MIX-AREN | SF-MIX-ASUB  |
| --- | --- | --- |
|  \( \hat{\Gamma} \) sctx @ m | \( \vdash_{\text{sf}} \bar{\sigma} \) seq(\( \hat{\Delta} \to \hat{\Xi} \)) @ m | \( \vdash_{\text{sf}} \bar{\sigma} \) seq(\( \hat{\Delta} \to \hat{\Xi} \)) @ m  |
|  \( \vdash_{\text{sf}} \) id\( ^{\text{m}} \) seq(\( \hat{\Gamma} \to \hat{\Gamma} \)) @ m | \( \vdash_{\text{sf}} \tau \) aren(\( \hat{\Gamma} \to \hat{\Delta} \)) @ m | \( \vdash_{\text{sf}} \tau \) asub(\( \hat{\Gamma} \to \hat{\Delta} \)) @ m  |
|   | \( \vdash_{\text{sf}} \bar{\sigma} \) @aren \( \tau \) seq(\( \hat{\Gamma} \to \hat{\Xi} \)) @ m | \( \vdash_{\text{sf}} \bar{\sigma} \) @asub \( \tau \) seq(\( \hat{\Gamma} \to \hat{\Xi} \)) @ m  |

\[
\left(\mathrm{id} ^ {\mathrm{m}}\right) ^ {+} := \mathrm{id} ^ {\mathrm{m}} \quad \left(\bar {\sigma} @ _ {\text {aren}} \tau\right) ^ {+} := \bar {\sigma} ^ {+} @ _ {\text {aren}} \tau^ {+} \quad \left(\bar {\sigma} @ _ {\text {asub}} \tau\right) ^ {+} := \bar {\sigma} ^ {+} @ _ {\text {asub}} \tau^ {+}
\]

\[
\mathrm{id} ^ {\mathrm{m}}. \widehat {\mathbf {m}} _ {\mu} := \mathrm{id} ^ {\mathrm{m}} \quad \left(\bar {\sigma} @ _ {\text {aren}} \tau\right). \widehat {\mathbf {m}} _ {\mu} := \bar {\sigma}. \widehat {\mathbf {m}} _ {\mu} @ _ {\text {aren}} \tau . \widehat {\mathbf {m}} _ {\mu} \quad \left(\bar {\sigma} @ _ {\text {asub}} \tau\right). \widehat {\mathbf {m}} _ {\mu} := \bar {\sigma}. \widehat {\mathbf {m}} _ {\mu} @ _ {\text {asub}} \tau . \widehat {\mathbf {m}} _ {\mu}
\]

\[
t \left[ \mathrm{id} ^ {\mathrm{m}} \right] _ {\text {seq}} := t \quad t \left[ \bar {\sigma} @ _ {\text {aren}} \tau \right] _ {\text {seq}} := t \left[ \bar {\sigma} \right] _ {\text {seq}} \left[ \tau \right] _ {\text {aren}} \quad t \left[ \bar {\sigma} @ _ {\text {asub}} \tau \right] _ {\text {seq}} := t \left[ \bar {\sigma} \right] _ {\text {seq}} \left[ \tau \right] _ {\text {asub}}
\]

\[
\bar {\sigma} \cdot \cdot := \bar {\sigma} \quad \bar {\sigma} \cdot (\Phi \cdot \mu) := (\bar {\sigma} \cdot \Phi) ^ {+} \quad \bar {\sigma} \cdot (\Phi \cdot \widehat {\mathbf {m}} _ {\mu}) := (\bar {\sigma} \cdot \Phi) \cdot \widehat {\mathbf {m}} _ {\mu}
\]

Figure 10 Definition of mixed sequences of atomic rensubs and associated operations of lifting, locking and application to an SFMTT expression. We also show how to apply a scoping telescope to a mixed sequence.

substituted variables after extending the context with an arbitrary lock telescopes instead of a scoping telescope. However, in order to prove this proposition we will need some auxiliary results.

First of all, we will formulate a generalisation of Proposition 3 that applies to sequences consisting of both atomic renamings and atomic substitutions. This generalisation is needed in the proof of Proposition 12, but also in the completeness proof itself. We define such mixed sequences in Figure 10. That figure also contains definitions for the operations of lifting a sequence, applying a lock to a sequence, applying a sequence to an SFMTT expression, and applying a scoping telescope to a sequence. These operations just apply the corresponding operations to the constituent atomic renamings and substitutions. To distinguish a mixed sequence from atomic or regular rensubs, we will refer to such a sequence with an overlined Greek letter (so e.g. \(\bar{\sigma}\)).

▶ Proposition 4. Let  \( \vdash_{sf} \bar{\sigma}, \bar{\tau} \operatorname{seq}(\hat{\Gamma} \to \hat{\Delta}) @ m \)  be two mixed sequences of atomic renamings and substitutions and suppose that  \( v [\bar{\sigma}. \Phi]_{\operatorname{seq}} = v [\bar{\tau}. \Phi]_{\operatorname{seq}} \)  for every scoping telescope  \( \Phi : s\operatorname{Tele}(m \to n) \)  and every variable  \( \hat{\Delta}. \Phi \vdash_{sf} v \operatorname{var} @ n \) . Then  \( t [\bar{\sigma}]_{\operatorname{seq}} = t [\bar{\tau}]_{\operatorname{seq}} \)  for every SFMTT expression  \( \hat{\Delta} \vdash_{sf} t \operatorname{expr} @ m \) .

Proof. The reasoning is exactly the same as in the proof of Proposition 3.

#### 4.1.3 Action of Lifted Atomic Rensubs on Variables

\(\triangleright\) Lemma 5. Given an atomic renaming \(\vdash_{\mathrm{sf}} \sigma \operatorname{aren}(\hat{\Gamma} \to \hat{\Delta}) @ m\) and a lock telescope \(\Lambda: \operatorname{LockTele}(m \to n)\), we have that \(\mathbf{v}_0^\alpha [\sigma^+]_{\mathrm{aren}}^\Lambda = \mathbf{v}_0^\alpha\) and \(\operatorname{suc}(v) [\sigma^+]_{\mathrm{aren}}^\Lambda = \operatorname{suc}\left(v [\sigma]_{\mathrm{aren}}^\Lambda\right)\). Note that we will no longer include var in the subscript of \(v [\sigma]_{\mathrm{aren},\mathrm{var}}^\Lambda\) but just write \(v [\sigma]_{\mathrm{aren}}^\Lambda\).

Proof. Recall that \(\sigma^{+}\) is defined as \(\mathrm{weaken}(\sigma).\mathbf{v}_{0}^{1_{\mu}}\). We can then compute that

\[
\mathbf {v} _ {0} ^ {\alpha} \left[ \sigma^ {+} \right] _ {\text {aren}} ^ {\Lambda} = \mathbf {v} _ {0} ^ {\alpha} \left[ \text {weaken} (\sigma). \mathbf {v} _ {0} ^ {1 _ {\mu}} \right] _ {\text {aren}} ^ {\Lambda} = \mathbf {v} _ {0} ^ {1 _ {\mu}} [ \alpha ] _ {2 - \text {cell}} ^ {\widehat {\mathbf {m}} _ {\mu} \Rightarrow \Lambda},
\]

where the last step makes use of Equation (20). By the definition of \(\_ [\_]_{2 - \text{cell}}^{\Rightarrow}\) (see Equation (14)), this last expression is equal to \(\mathbf{v}_0^{(1_1\star \alpha)\circ 1_\mu}\). From the laws of a strict 2-category, it follows that \((1_1\star \alpha)\circ 1_\mu = \alpha\) so the variable we obtain is really \(\mathbf{v}_0^\alpha\).