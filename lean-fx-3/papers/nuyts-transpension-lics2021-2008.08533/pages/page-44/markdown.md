16:44

A. Nuyts and D. Devriese

Vol. 20:2

Binary and destrictified reformulation of the original \(\Phi\)-rule [BCM15, Mou16, CH21]:

\(\Delta, i: \mathbb{I} \vdash B \text{ type}\)

\(\Delta, i: \mathbb{I}, y: B \vdash C \text{ type}\)

\(\Delta, y: B[\epsilon / i] \vdash c_{\epsilon}: C[\epsilon / i]\) (\(\epsilon \in \{0, 1\}\))

\(\Delta, h: \forall (i: \mathbb{I}).B, i: \mathbb{I} \vdash c_{\forall}: C[h i / y]\)

\(\Delta, h: \forall (i: \mathbb{I}).B \vdash c_{\forall}[\epsilon / i] = c_{\epsilon}[h \epsilon / y]: C[h \epsilon / y]\) (\(\epsilon \in \{0, 1\}\))

\(\Delta \vdash \Phi c_0 c_1 c_{\forall}: \forall i.(y: B) \to C\)

where \(\Phi c_0 c_1 c_{\forall} \epsilon b = c_{\epsilon}[b / y]\) (\(\epsilon \in \{0, 1\}\))

\(\Delta, i: \mathbb{I} \vdash \Phi c_0 c_1 c_{\forall} i b = c_{\forall}[\lambda i.b / h]\)

\(\Phi\) -rule in MTraS (recall Eq. (3.1)):

PHI
\(\mathbb{X}, u: \mathbb{U} \mid \Gamma \vdash C \text{ type}\)
\(\mathbb{X}, u: \mathbb{U} \mid \Gamma, -: u \in \partial \mathbb{U} \vdash c_{\partial}: C\)
\(\mathbb{X}, u: \mathbb{U} \mid \Gamma, \widehat{\mathbb{Q}}_{[u]}^{\forall u}, \widehat{\mathbb{Q}}_{[u]}^{\exists [u]} \vdash c_{\forall}: C[\widehat{\mathbb{Q}}_{\text{reidx}_u: 1 \Rightarrow [u] \circ \forall u \Rightarrow 1}]\)
\(\mathbb{X}, u: \mathbb{U} \mid \Gamma, \widehat{\mathbb{Q}}_{[u]}^{\forall u}, \widehat{\mathbb{Q}}_{[u]}^{\exists [u]}, -: u \in \partial \mathbb{U} \vdash c_{\forall} = c_{\partial}[\widehat{\mathbb{Q}}_{\text{reidx}_u}^{\text{app}_u}] : C[\widehat{\mathbb{Q}}_{\text{reidx}_u}^{\text{app}_u}]\)
\(\overline{\mathbb{X}, u: \mathbb{U} \mid \Gamma \vdash \Phi_u c_\partial c_\forall}: C}\)
where \(\mathbb{X}, u: \mathbb{U} \mid \Gamma, -: u \in \partial \mathbb{U} \vdash \Phi_u c_\partial c_\forall = c_{\partial}: C\)
\(\mathbb{X}, u: \mathbb{U} \mid \Delta, \widehat{\mathbb{Q}}_{[u]}^{\exists [u]} \vdash \Phi_u c_\partial c_\forall = c_{\forall}[\widehat{\mathbb{Q}}_{\text{unmer}_u: \forall u \circ [u] \Rightarrow 1}^{\text{const}_u: 1 \Rightarrow \forall u \circ [u]}, \widehat{\mathbb{Q}}_{[u]}^{\exists [u]}] : C\)

Figure 10: The \(\Phi\)-rule (sound if \(\mathbb{U}\) is \(\top\)-slice fully faithful and shard-free).

only on i and variables fresh for i, then the variable i can be captured in b yielding a section  \( \lambda i.b : \forall i.Bi \)  to which we can apply the action on sections  \( c_{\forall} \) .

A few remarks are necessary in order to move to MTraS. First of all, note that the fully applied conclusion of the \(\Phi\)-rule is \(\Delta, i: \mathbb{I}, y: B \vdash \Phi c_0 c_1 c_\forall i y: C\). Of course the endpoints together constitute the boundary of the interval, so if we want to generalize away from cubical type theory, we can expect something like \(\Delta, u: \mathbb{U}, y: B \vdash \Phi c_\partial c_\forall u y: C\). We will assume that the shape \(\mathbb{U}\) is \(\top\)-slice fully faithful and shard-free. In order to translate the context (\(\Delta, u: \mathbb{U}, y: B\)) to MTraS, recall that in FFTraS (as well as in the BCM system) the variables to the left of \(u\) are fresh for \(u\), whereas those to the right need not be. In MTraS we put the shape variables in the shape context, so the context translates to (\(\Delta, \widehat{\mathbb{Q}}_{[u]}^{\exists[u]}, y: B\)). In MTraS we will treat this entire thing as a single abstract context \(\Gamma\), so we do not grant the domain of the \(\Phi\)-function any special status; in a way all of \(\Gamma\) takes the role of \(B\).

Then, completely analogously to BCM, we need a type C in context  \( \Gamma \) , an object  \( c_{\partial}:C \)  whenever u is on the boundary, and a compatible action  \( c_{\forall} \)  that acts on sections of  \( \Gamma \)  and produces sections of C, but the quantifier  \( \forall u \)  has been brought to the left as  \( \widehat{\mathbb{Q}}_{[u]}^{\exists[u]} \) . Again the resulting term  \( \Phi_{u}c_{\partial}c_{\forall} \)  reduces to  \( c_{\partial} \)  when on the boundary, and to  \( c_{\forall} \)  when all variables in use are fresh for u. Again, the computation rule for sections is in a non-general context and needs to be forcibly closed under substitution, but see Remark 9.4.

Note that the FFTraS/BCM substitutions \(hi / b\) and \(h\epsilon /b\) (i.e. \(hi / b\) where \(i\) is on the boundary) involving applications, all turn into usages of \(\widehat{\mathbb{Q}}_{\mathrm{reidx}_u}^{\mathrm{app}_u}\) whereas the variable capturing substitution \(\lambda i.b / h\) has turned into \((\widehat{\mathbb{Q}}_{\mathrm{unmer}_u}^{\mathrm{const}_u},\widehat{\mathbb{Q}}_{[u]}^{\exists [u]}):(\Delta ,\widehat{\mathbb{Q}}_{[u]}^{\exists [u]})\to (\Delta ,\widehat{\mathbb{Q}}_{[u]}^{\exists [u]},\widehat{\mathbb{Q}}_{[u]}^{\forall u},\widehat{\mathbb{Q}}_{[u]}^{\exists [u]})\) which