18-4

Semantics of multimodal adjoint type theory

\[
\frac {}{\diamond_ {p} \operatorname{ctx} _ {p}} \qquad \frac {\Gamma \operatorname{ctx} _ {q} \quad \mu : p \to q}{\Gamma / \mu \operatorname{ctx} _ {p}} \qquad \frac {\Gamma \operatorname{ctx} _ {q} \quad \mu : p \to q \text {tangible} \quad \Gamma / \mu \vdash A \operatorname{type} _ {p}}{(\Gamma , x : ^ {\mu} A) \operatorname{ctx} _ {q}}
\]

\[
\frac {\Gamma \operatorname{ctx} _ {r} \qquad \mu : q \to r \qquad \nu : p \to q}{\Gamma / _ {\mu} / _ {\nu} = \Gamma / _ {\{\mu \circ \nu \}}} \qquad \frac {\Gamma \operatorname{ctx} _ {p}}{\Gamma / _ {1 _ {p}} = \Gamma} \qquad \frac {\theta : \Gamma \to_ {q} \Delta \qquad \mu , \nu : p \to q \qquad \alpha : \mu \Rightarrow \nu}{\theta / _ {\alpha} : \Gamma / _ {\nu} \to_ {p} \Delta / _ {\mu}}
\]

Fig. 2. Contexts and substitutions in MATT

\[
\begin{array}{l} \operatorname{locks} \left(\diamond_ {p}\right) = 1 _ {p} \quad \operatorname{locks} \left(\Gamma , x: ^ {\mu} A\right) = \operatorname{locks} (\Gamma) \quad \operatorname{locks} \left(\Gamma / _ {\mu}\right) = \operatorname{locks} (\Gamma) \circ \mu \\ \frac {\alpha : \mu \Rightarrow \operatorname{locks} (\Delta)}{\Gamma , x : ^ {\mu} A , \Delta \vdash x ^ {\alpha} : A [ \uparrow^ {\alpha} ]} \quad \frac {\alpha : \mu \Rightarrow \operatorname{locks} (\Delta) \circ \nu \quad \beta : \nu \Rightarrow \varrho}{(\Gamma , x : ^ {\mu} A , \Delta) / _ {\varrho} \vdash x ^ {\alpha} [ 1 _ {(\Gamma , x : ^ {\mu} A , \Delta)} / _ {\beta} ] = x ^ {(\operatorname{locks} (\Delta) \circ \beta) \circ \alpha}} \\ \end{array}
\]

Fig. 3. Variables in MATT

\[
\frac {\mu : p \to q \text { sharp } \qquad \Gamma / _ {\mu} \vdash A \text { type } _ {p} \qquad \Gamma , x : ^ {\mu} A \vdash B \text { type } _ {q}}{\Gamma \vdash (x : ^ {\mu} A) \to B \text { type } _ {q}}
\]

\[
\frac {\mu : p \to q \text { sharp } \qquad \Gamma / _ {\mu} \vdash A \text { type } _ {p} \qquad \Gamma , x : ^ {\mu} A \vdash b : B}{\Gamma \vdash (\lambda x . b) : (x : ^ {\mu} A) \to B}
\]

\[
\frac {\mu : p \to q \text { sharp } \qquad \Gamma \vdash f : (x : ^ {\mu} A) \to B \qquad \Gamma / _ {\mu} \vdash a : A}{\Gamma \vdash f   a : B [ x \leftarrow a ]}
\]

\[
\frac {\mu : p \to q \text { sharp } \qquad \Gamma , x : ^ {\mu} A \vdash b : B \qquad \Gamma / _ {\mu} \vdash a : A}{\Gamma \vdash (\lambda x . b)   a = b [ x \leftarrow a ] : B [ x \leftarrow a ]} \qquad \frac {\mu : p \to q \text { sharp } \qquad \Gamma , x : ^ {\mu} A \vdash f   x = g   x : B}{\Gamma \vdash f = g : (x : ^ {\mu} A) \to B}
\]

Fig. 4. Modal function-types in MATT

(4) Every sinister morphism generates a negative modal operator. These are not in MTT. Their rules are shown in Figure 6; they simplify those of [11] by using right adjoints instead of parametric ones.

Remark 2.2 If \(\mu\) is both sharp and sinister, the formation and introduction rules of \(\mu \diamondsuit A\) are identical to those of \(\mu^{\dagger} \boxdot A\). Daniel Gratzer has shown that \(\mu \diamondsuit A\) actually satisfies all the rules of \(\mu^{\dagger} \boxdot A\), while conversely if \(\mu\) is transparent then \(\mu^{\dagger} \boxdot A\) satisfies all the rules of \(\mu \diamondsuit A\) except definitional \(\eta\)-conversion.

The flexibility in choosing the tangible, sharp, transparent, and sinister morphisms allows us to compare MATT easily to other modal type theories.

(i) If \(\mathcal{M}\) is any 2-category, and we take all morphisms to be tangible, sharp, and transparent, but none to be sinister, then MATT reduces to MTT.
(ii) For any 2-category \(\mathcal{L}\), let \(\mathcal{M} = \mathcal{L}[\dagger \mathcal{L}]\) be obtained by formally adjoining a left adjoint \(\dagger \mu\) to each \(\mu\) in \(\mathcal{L}\). We take only identities to be tangible, sharp, and transparent, and the sinister morphisms to be these left adjoints \(\dagger \mu\); then MATT reduces to FitchTT [11] over \(\mathcal{L}\) with actual left adjoints.
(iii) The closest match with theories such as [27,37,31] occurs when \(\mathcal{M} = \mathcal{L}[\mathcal{L}^{\dagger}]\) is obtained by formally adjoining a right adjoint \(\mu^{\dagger}\) to each morphism \(\mu\) of \(\mathcal{L}\). In this case we take the tangible, sharp, and sinister morphisms to be the image of \(\mathcal{L}\) in \(\mathcal{L}[\mathcal{L}^{\dagger}]\); thus all the modal operators come in adjoint pairs. Different theories make different choices about transparency: in [37] only identities are transpar