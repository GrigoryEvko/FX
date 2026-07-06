Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:37

Application is translated using Proposition 3.3. Let \(\Theta = \Gamma, u: \mathbb{U}, \delta: \Delta\) with no shape variables in \(\Delta\). Then \(\{\Theta\} = \{\Gamma\}, u: \mathbb{U}\) and \(\langle \Theta \rangle = \langle \Gamma \rangle, \widehat{\mathbf{a}}_{\forall u}^{\exists [u]}, \langle \Delta \rangle\).

FF:FORALL:ELIM

\[
\begin{array}{l} \{\Gamma \} \mid \langle \Gamma \rangle \vdash f: \langle \forall u \mid \langle A \rangle \rangle \\ \frac {\{\Gamma \} \mid \langle \Gamma \rangle , \widehat {\mathbf {a}} _ {\forall u \circ \exists [ u ]} ^ {\exists u \circ \exists [ u ]} \vdash f [ \widehat {\mathbf {a}} _ {\text {const} _ {u}} ^ {\text {drop} _ {u}} ] : \left\langle \forall u \mid \langle A \rangle [ \widehat {\mathbf {a}} _ {\text {const} _ {u}} ^ {\text {drop} _ {u}}, \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]} ] \right\rangle}{\{\Gamma \} \mid \langle \Gamma \rangle , \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]} , \langle \Delta \rangle , \widehat {\mathbf {a}} _ {\exists [ u ]} ^ {\exists u} \vdash f [ \widehat {\mathbf {a}} _ {\text {const} _ {u}} ^ {\text {drop} _ {u}} ] : \left\langle \forall u \mid \langle A \rangle [ \widehat {\mathbf {a}} _ {\text {const} _ {u}} ^ {\text {drop} _ {u}}, \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]} ] \right\rangle} \\ \frac {\{\Gamma \} , u : \mathbb {U} \mid \langle \Gamma \rangle , \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]} , \langle \Delta \rangle \vdash \mathsf {a p p} _ {u} \cdot_ {\exists [ u ]} f [ \widehat {\mathbf {a}} _ {\text {const} _ {u}} ^ {\text {drop} _ {u}} ] : \langle A \rangle [ \widehat {\mathbf {a}} _ {\text {const} _ {u}} ^ {\text {drop} _ {u}}, \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]} ] [ \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]}, \widehat {\mathbf {a}} _ {\text {app} _ {u}} ^ {\text {copy} _ {u}} ] = \langle A \rangle}{\end{array}
\]

Observe that, lacking existential quantification for contexts in Section 2, the application rule FF:FORALL:ELIM simply discarded the non-fresh part \(\Delta\). In the target language, variables under \(\widehat{\mathbf{a}}_{\exists [u]}^{\exists u}\) can only be used if they are annotated with a modality \(\mu\) from which there is a 2-cell \(\alpha : \mu \Rightarrow \exists [u]\), i.e. if they are fresh for \(u\). However, recall that the word 'fresh' needs to be taken with a grain of salt when we are not dealing with a \(\top\)-slice fully faithful shape. For example, if \(\mathbb{U}\) is cartesian, then \(\widehat{\mathbf{a}}_{\exists [u]}^{\exists u} = \widehat{\mathbf{a}}_{\Omega [u]}^{\Sigma u}\), so that the aggregation of shape and type context in the premise and conclusion of the app\(_u\)-rule

\[
\frac {\mathbb {X} , \mid \Gamma , \widehat {\mathbf {a}} _ {\Omega [ u ]} ^ {\Sigma u} \vdash f : \langle \Pi   u \mid A \rangle}{\mathbb {X} , u : \mathbb {U} \mid \Gamma \vdash \mathsf {a p p} _ {u} \cdot_ {\Omega [ u ]} f : A [ \widehat {\mathbf {a}} _ {\mathsf {a p p} _ {u}} ^ {\mathsf {c o p y} _ {u}} ]}
\]

are isomorphic: \(\llbracket \mathbb{X}\rrbracket .(\Sigma (\mathbf{y}U).\llbracket \Gamma \rrbracket)\cong (\llbracket \mathbb{X}\rrbracket \times \mathbf{y}U).\llbracket \Gamma \rrbracket .\)

7.1.5. Telescope quantification. Let \(\Theta = (\Gamma, u: \mathbb{U}, \delta: \Delta)\) with no shape variables in \(\Delta\). Then \([\forall u] \Theta = (\Gamma, \forall u. (\delta: \Delta))\). We translate this as follows:

\[
\{[ \forall u ] \Theta \} = \{\Gamma , \forall u. (\delta : \Delta) \} = \{\Gamma \} \quad \langle [ \forall u ] \Theta \rangle = \langle \Theta \rangle , \widehat {\mathbf {a}} _ {\{u \}} ^ {\forall u} \quad (\text {FF:CTX - FORALL})
\]

Let \(\rho = (\sigma, u / u, \tau / \delta') : \Theta = (\Gamma, u : \mathbb{U}, \delta : \Delta) \to \Theta' = (\Gamma', u : \mathbb{U}, \delta' : \Delta')\). Then \([\forall (u / u)]\rho = (\sigma, \lambda u.\tau / \lambda u.\delta')\). We translate this as follows:

\[
\{[ \forall (u / u) ] \rho \} = \left\{\sigma , \lambda u. \tau / \lambda u. \delta^ {\prime} \right\} = \{\sigma \} \quad \langle [ \forall (u / u) ] \rho \rangle = \langle \rho \rangle , \widehat {\mathbf {a}} _ {\{u \}} ^ {\forall u} \quad (\text {FF:CTX - FORALL:FMAP})
\]

The rule FF:CTX-FORALL:NIL concerns  \( (\Gamma,\forall u.())=\forall u \)  which translates to  \( \{\Gamma\}\mid\langle\Gamma\rangle,\widehat{\mathbf{a}}_{\forall u}^{\exists[u]},\widehat{\mathbf{a}}_{\{u\}}\forall u \)  ctx, which is isomorphic to  \( \{\Gamma\}\mid\langle\Gamma\rangle \)  ctx by the 2-cell  \( (1_{\Gamma},\widehat{\mathbf{a}}_{\text{unmer}_{u}:\forall u\circ\{u\}\Rightarrow1}^{\text{const}_{u}:1\Rightarrow\forall u\circ\exists[u]}) \)  because U is T-slice fully faithful (quantification Theorem 6.31). Naturality of  \( a_{unmer_{u}}^{const_{u}} \)  models FF:CTX-FORALL:FMAP:NIL.

7.1.6. Telescope application. Let \(\Theta = (\Gamma, u: \mathbb{U}, \delta: \Delta)\) with no shape variables in \(\Delta\). Then \(\mathsf{app}_{\Theta} = (u / u, (\lambda u.\delta) u / \delta): ([\forall u] \Theta, u: \mathbb{U}) = (\Gamma, \forall u. (\delta: \Delta), u: \mathbb{U}) \to \Theta\). We translate this using the 2-cell

\[
\{\Gamma \}, u: \mathbb {U} \mid \langle \mathsf {a p p} _ {\Theta} \rangle = (\widehat {\mathbf {a}} _ {\text {reidx} _ {u}: 1 \Rightarrow \{u \} \circ \forall u} ^ {\text {app} _ {u}: \exists [ u ] \circ \forall u \Rightarrow 1}): (\langle \Theta \rangle , \widehat {\mathbf {a}} _ {\{u \}} ^ {\forall u}, \widehat {\mathbf {a}} _ {\{u \}} ^ {\exists [ u ]}) \to \langle \Theta \rangle \quad (\text {FF:CTX - APP})
\]

naturality of which models FF:CTX-APP:NAT.

If \(\Delta\) is empty, then \(\langle \Theta \rangle = (\langle \Gamma \rangle ,\widehat{\mathbf{a}}_{\forall u}^{\exists [u]})\), so that

\[
\begin{array}{l} \{\Gamma \}, u: \mathbb {U} \mid \left\langle \mathsf {a p p} _ {(\Gamma , u: \mathbb {U})} \right\rangle = (\widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]}, \widehat {\mathbf {a}} _ {\text {reidx} _ {u}} ^ {\text {app} _ {u}}) = (\widehat {\mathbf {a}} _ {\text {unmer} _ {u} ^ {- 1}} ^ {\text {const} _ {u} ^ {- 1}}, \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]}) \\ : (\langle \Gamma \rangle , \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]}, \widehat {\mathbf {a}} _ {\{u \}} ^ {\forall u}, \widehat {\mathbf {a}} _ {\{u \}} ^ {\exists [ u ]}) \to (\langle \Gamma \rangle , \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]}) \\ \end{array}
\]