18

A Substitution Algorithm for Multimode Type Theory: Technical Report

### 4.2 Preservation of Observational Equivalence of SFMTT Substitutions

Definition 2 tells us that two SFMTT substitutions are observationally equivalent if they yield equal results when applied to any expression. It is not immediately clear that this property is preserved by some of the operations that act on substitutions, such as \(\widehat{\mathbf{a}}_{\mu}\) or lifting. The following lemmas tell us that this is indeed the case.

▶ Lemma 14. Let \(\vdash_{\mathrm{sf}} \sigma, \tau \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ n\) be two SFMTT substitutions and \(\mu : m \to n\) a modality. If \(\sigma \approx^{\mathrm{obs}} \tau\), then also \(\sigma \cdot \widehat{\mathbf{a}}_{\mu} \approx^{\mathrm{obs}} \tau \cdot \widehat{\mathbf{a}}_{\mu}\).

Proof. Take an arbitrary expression \(\hat{\Delta} \cdot \widehat{\mathbf{a}}_{\mu} \vdash_{\mathrm{sf}} t \exp @ m\). Then we can apply SF-EXPR-MOD-TM to see that \(\hat{\Delta} \vdash_{\mathrm{sf}} \operatorname{mod}_{\mu}(t) \exp @ n\). Hence, since \(\sigma \approx^{\mathrm{obs}} \tau\), the definition of observational equivalence tells us that \((\operatorname{mod}_{\mu}(t)) [\sigma]_{\mathrm{sub}} = (\operatorname{mod}_{\mu}(t)) [\tau]_{\mathrm{sub}}\). Since applying a lock to a regular SFMTT substitution amounts to applying the lock to all its constituent atomic substitutions, it follows that \((\operatorname{mod}_{\mu}(t)) [\sigma]_{\mathrm{sub}} = \operatorname{mod}_{\mu}(t [\sigma, \widehat{\mathbf{a}}_{\mu}]_{\mathrm{sub}})\) (and similarly for \(\tau\)). We therefore have that \(\operatorname{mod}_{\mu}(t [\sigma, \widehat{\mathbf{a}}_{\mu}]_{\mathrm{sub}}) = \operatorname{mod}_{\mu}(t [\tau, \widehat{\mathbf{a}}_{\mu}]_{\mathrm{sub}})\) and by injectivity of expression constructors it follows that \(t [\sigma, \widehat{\mathbf{a}}_{\mu}]_{\mathrm{sub}} = t [\tau, \widehat{\mathbf{a}}_{\mu}]_{\mathrm{sub}}\). As this holds for arbitrary \(t\), we have proven that \(\sigma \cdot \widehat{\mathbf{a}}_{\mu} \approx^{\mathrm{obs}} \tau \cdot \widehat{\mathbf{a}}_{\mu}\).

▶ Lemma 15. Let \(\vdash_{\mathrm{sf}} \sigma, \tau \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m\) be two SFMTT substitutions. If \(\sigma \approx^{\mathrm{obs}} \tau\), then also \(\sigma^{+} \approx^{\mathrm{obs}} \tau^{+}\).

Proof. We can apply the same reasoning as in the proof of Lemma 14, but with the expression constructor \(\lambda^{\mu}(\_)\) instead of \(\mathrm{mod}_{\mu}(\_)\).

▶ Corollary 16. If  \( \vdash_{sf} \sigma, \tau \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m \)  are two SFMTT substitutions and  \( \Phi : s\text{Tele}(m \to n) \)  is a scoping telescope, then  \( \sigma \approx^{obs} \tau \)  implies  \( \sigma \cdot \Phi \approx^{obs} \tau \cdot \Phi \) .

We note that the converse of Proposition 3 immediately follows from Corollary 16. Furthermore, if we restrict the scoping telescopes in this corollary to lock telescopes, the converse of Proposition 12 can also be derived.

### 4.3 Relating WSMTT and SFMTT Lifting

▶ Lemma 17. Given a WSMTT substitution \(\vdash_{\mathrm{ws}} \sigma \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m\), we have \([\sigma^{+}] \approx^{\mathrm{obs}} [\sigma]^{+}\).

Proof. First of all, we can calculate that

\[
\begin{array}{l} [ [ \sigma^ {+} ] ] = [ [ (\sigma \circ \pi). \mathbf {v} _ {0} ] ] \quad \text {(Definition of } ^ {+}, \text { Equation(1))} \\ = \llbracket \sigma \circ \pi \rrbracket^ {+} * (\mathrm{id} ^ {\mathrm{a}}. \llbracket \mathbf {v} _ {0} \rrbracket) \quad (\text {Definition of} [ \llbracket ]) \\ = \left(\llbracket \sigma \rrbracket + + \llbracket \pi \rrbracket\right) ^ {+} * \left(\mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}}\right) \quad (\text {Definition of} [ \llbracket ]) \\ = \llbracket \sigma \rrbracket^ {+} * \pi^ {+} * \left(\mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}}\right). \\ \end{array}
\]

The last step combines the definition of \(\llbracket \pi \rrbracket\) with the fact that lifting a regular substitution amounts to lifting all of its constituent substitutions. By the definition of \(\approx^{\mathrm{obs}}\) it now suffices to prove that \(t[\pi^{+}]_{\mathrm{asub}}\left[\mathrm{id}^{\mathrm{a}}.\mathbf{v}_{0}^{1_{\mu}}\right]_{\mathrm{asub}} = t\) for every expression \(\hat{\Gamma}.\mu \vdash_{\mathrm{sf}}t\) expr \(@ m\). For this we use Proposition 11, so we have to show that \(v[\pi^{+}.\Lambda ]_{\mathrm{asub}}\left[\left(\mathrm{id}^{\mathrm{a}}.\mathbf{v}_{0}^{1_{\mu}}\right).\Lambda \right]_{\mathrm{asub}} = v\) for every lock telescope \(\Lambda :\operatorname {LockTele}(m\to n)\) and every variable \(\hat{\Gamma}.\mu .\Lambda \vdash_{\mathrm{sf}}v\) var \(@ n\). We distinguish between two cases for the variable \(v\).