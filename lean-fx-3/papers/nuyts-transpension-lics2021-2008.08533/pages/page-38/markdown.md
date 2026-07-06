16:38

A. Nuyts and D. Devriese

Vol. 20:2

Now \(\mathbf{Q}_{\mathrm{unmer}_u}^{\mathrm{const}_u}\) models the equation in FF:CTX-FORALL:NIL which well-typedness of FF:CTX-APP:NIL relies on, so it can be regarded as the identity and the above essentially models FF:CTX-APP:NIL.

Similarly, the rule FF:CTX-FORALL:FMAP:CTX-APP concerns  \( [\forall u/u]app_{\Theta} \) , which translates to

\[
\{\Gamma \} \mid (\langle \mathsf {a p p} _ {\Theta} \rangle , \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u}) = (\mathbf {a} _ {\text {reid} x _ {u}} ^ {\text {app} _ {u}}, \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u}) = (\widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u}, \mathbf {a} _ {\text {unmer} _ {u} ^ {- 1}} ^ {\text {const} _ {u} ^ {- 1}})
\]

\[
: (\langle \Theta \rangle , \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u}, \widehat {\mathbf {a}} _ {\forall u} ^ {\mathbb {Q} [ u ]}, \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u}) \to (\langle \Theta \rangle , \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u}),
\]

essentially modelling FF:CTX-FORALL:FMAP:CTX-APP.

7.1.7. Transpension type. Let \(\Theta = (\Gamma, u : \mathbb{U}, \delta : \Delta)\) with no shape variables in \(\Delta\). The transpension type translates to a modal type:

FF:TRANSP

\[
\frac {\{\Gamma \} \mid \langle \Theta \rangle , \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u} \vdash \langle A \rangle \text {type}}{\{\Gamma \} , u : \mathbb {U} \mid \langle \Theta \rangle \vdash \langle \mathbb {Q} [ u ] \mid \langle A \rangle \rangle \text {type}}
\]

FF:TRANSP:INTRO

\[
\frac {\{\Gamma \} \mid \langle \Theta \rangle , \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u} \vdash \langle a \rangle : \langle A \rangle}{\{\Gamma \} , u : \mathbb {U} \mid \langle \Theta \rangle \vdash \operatorname{mod} _ {\mathbb {Q} [ u ]} a : \langle \mathbb {Q} [ u ] \mid \langle A \rangle \rangle}
\]

The eliminator is translated using Proposition 3.3.

FF:TRANSP:ELIM

\[
\frac {\{\Gamma \} , u : \mathbb {U} \mid \langle \Gamma \rangle , \widehat {\mathbf {a}} _ {\mathbb {U}} ^ {\mathbb {Q} [ u ]} \vdash t : \left\langle \forall u \mid \langle A \rangle [ \widehat {\mathbf {a}} _ {\text {unmer} _ {u} ^ {- 1}} ^ {\text {const} _ {u} ^ {- 1}} ] \right\rangle}{\{\Gamma \} \mid \langle \Gamma \rangle \vdash \text {unmer} _ {u} \cdot_ {\forall u} t : \langle A \rangle}
\]

Again \(\mathbf{Q}_{\mathrm{unmer}_u^{-1}}^{\mathrm{const}_u^{-1}}\) just models FF:CTX-FORALL:NIL and can be ignored. The \(\beta\)- and \(\eta\)-rules are the ones form Proposition 3.3, and the naturality rules amount to

\[
(\mathsf {m o d} _ {\forall u} \langle a \rangle) [ \langle \rho \rangle ] = \mathsf {m o d} _ {\forall u} \left(\langle a \rangle \Big [ \langle \rho \rangle , \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u} \Big ]\right), \qquad \langle \forall u | \langle A \rangle \rangle [ \langle \rho \rangle ] = \Big \langle \forall u | \langle A \rangle \Big [ \langle \rho \rangle , \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u} \Big ] \Big \rangle .
\]

This concludes the embedding for the selected typing rules in Fig. 1.

7.2. Internal transposition. In Section 2.3, we proved the isomorphism

\[
(\forall (u: \mathbb {U}). A) \rightarrow B \quad \cong \quad \forall (u: \mathbb {U}). (A \rightarrow \mathbb {Q} [ u ] B). \tag {7.1}
\]

The MTraS equivalent,

\[
(\forall u \mid A) \to B ^ {\prime} \quad \cong \quad \left\langle \forall u \mid A \to \left\langle \mathbb {Q} [ u ] \mid B ^ {\prime} [ \mathbf {a} _ {\text {unmer} _ {u} ^ {- 1}} ^ {\text {const} _ {u} ^ {- 1}} ] \right\rangle \right\rangle
\]

is not in general true (or even statable) but for \(\top\)-slice fully faithful multipliers it follows from the following instance of Proposition 3.4 (which holds in general)

\[
\left\langle \mathbb {Q} [ u ] \mid (\forall u \mid A [ \mathbf {a} _ {\text {reid} x _ {u}} ^ {\text {app} _ {u}} ]) \rightarrow B \right\rangle \quad \cong \quad (A \rightarrow \langle \mathbb {Q} [ u ] \mid B \rangle) \tag {7.2}
\]

by applying \(\langle \forall u\mid \sqcup \rangle\) to both sides, redefining \(B^{\prime} = B[\mathbf{a}_{\mathrm{unmer}_u}^{\mathrm{const}_u}]\) and using the quantification Theorem 6.31.