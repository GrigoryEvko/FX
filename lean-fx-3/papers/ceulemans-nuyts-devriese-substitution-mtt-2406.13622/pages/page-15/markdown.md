J. Ceulemans, A. Nuyts and D. Devriese

15

Proof. The proof is similar to that of Lemma 7. We make use of Proposition 4, and now we really have two sequences both consisting of an atomic renaming and an atomic substitution. Hence, we have to show that \( v[\pi \cdot \Phi]_{\mathrm{aren}}[\sigma^{+}\cdot \Phi]_{\mathrm{asub}} = v[\sigma \cdot \Phi]_{\mathrm{asub}}[\pi \cdot \Phi]_{\mathrm{aren}} \) for every variable \( \Delta \cdot \Phi \vdash_{\mathrm{st}} v \) var \( \otimes n \). We will do this by induction on the number of variables in the scoping telescope \( \Phi \).

CASE \(\Phi = \Lambda\), so \(\Phi\) contains no variables.

Now we can compute that

\[
\begin{array}{l} v [ \pi . \Lambda ] _ {\text { aren }} [ \sigma^ {+}. \Lambda ] _ {\text { asub }} = v [ \pi ] _ {\text { aren }} ^ {\Lambda} [ \sigma^ {+} ] _ {\text { asub }} ^ {\Lambda} \\ = \operatorname{suc} (v) [ \sigma^ {+} ] _ {\text { asub }} ^ {\Lambda} \\ = v [ \sigma ] _ {\text { asub }} ^ {\Lambda} [ \pi ] _ {\text { aren }} ^ {\Lambda} \tag {Lemma6} \\ = v [ \sigma . \Lambda ] _ {\text { asub }} [ \pi . \Lambda ] _ {\text { aren }}. \\ \end{array}
\]

CASE \(\Phi = \Phi^{\prime}\cdot \rho .\Lambda\)

We now have to distinguish two cases for the variable v.

CASE \(v = \mathbf{v}_0^\alpha\)

The computations go as follows.

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\alpha} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { aren }} \left[ \sigma^ {+}. \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { asub }} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ (\pi . \Phi^ {\prime}) ^ {+} \right] _ {\text { aren }} ^ {\Lambda} \left[ (\sigma^ {+}. \Phi^ {\prime}) ^ {+} \right] _ {\text { asub }} ^ {\Lambda} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ (\sigma^ {+}. \Phi^ {\prime}) ^ {+} \right] _ {\text { asub }} ^ {\Lambda} \tag {Lemma5} \\ = \mathbf {v} _ {0} ^ {\alpha} \quad (\text { Lemma   6 }) \\ \end{array}
\]

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\alpha} \left[ \sigma . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { asub }} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { aren }} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ (\sigma . \Phi^ {\prime}) ^ {+} \right] _ {\text { asub }} ^ {\Lambda} \left[ (\pi . \Phi^ {\prime}) ^ {+} \right] _ {\text { aren }} ^ {\Lambda} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ (\pi . \Phi^ {\prime}) ^ {+} \right] _ {\text { aren }} ^ {\Lambda} \tag {Lemma6} \\ = \mathbf {v} _ {0} ^ {\alpha} \quad (\text { Lemma   5 }) \\ \end{array}
\]

CASE \(v = \operatorname{suc}(v')\)

Now we can compute

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { aren }} \left[ \sigma^ {+}. \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { asub }} \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ (\pi . \Phi^ {\prime}) ^ {+} \right] _ {\text { aren }} ^ {\Lambda} \left[ (\sigma^ {+}. \Phi^ {\prime}) ^ {+} \right] _ {\text { asub }} ^ {\Lambda} \\ = \operatorname{suc} \left(v ^ {\prime} \left[ \pi . \Phi^ {\prime} \right] _ {\text {aren}} ^ {\Lambda}\right) \left[ (\sigma^ {+}. \Phi^ {\prime}) ^ {+} \right] _ {\text {asub}} ^ {\Lambda} \tag {Lemma5} \\ = v ^ {\prime} \left[ \pi . \Phi^ {\prime}. \Lambda \right] _ {\text {aren}} \left[ \sigma^ {+}. \Phi^ {\prime}. \Lambda \right] _ {\text {asub}} \left[ \pi . \Lambda \right] _ {\text {aren}} \tag {Lemma6} \\ \end{array}
\]

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \sigma . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {asub}} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ \left(\sigma . \Phi^ {\prime}\right) ^ {+} \right] _ {\text {asub}} ^ {\Lambda} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \\ = v ^ {\prime} \left[ \sigma . \Phi^ {\prime}. \Lambda \right] _ {\text {asub}} \left[ \pi . \Lambda \right] _ {\text {aren}} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \tag {Lemma6} \\ \end{array}
\]

The induction hypothesis with scoping telescope \(\Phi'.\Lambda\) (which has one variable less than \(\Phi\)) gives us that \(v'\left[\pi.\Phi'.\Lambda\right]_{\mathrm{aren}}\left[\sigma^{+}.\Phi'.\Lambda\right]_{\mathrm{asub}} = v'\left[\sigma.\Phi'.\Lambda\right]_{\mathrm{asub}}\left[\pi.\Phi'.\Lambda\right]_{\mathrm{aren}}\). The result then follows from Corollary 8 with \(t = v'\left[\sigma.\Phi'.\Lambda\right]_{\mathrm{asub}}\), \(\sigma = \pi\), \(\Phi_1 = \Phi'\), \(\mu = \rho\) and \(\Phi_2 = \Lambda\).

◀