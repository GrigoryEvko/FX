11:16

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

$$\boxed{\Gamma \vdash M : A @ m}$$

$$\frac{\mu : \operatorname{Hom}_{\mathcal{M}}(n, m) \quad \Gamma \operatorname{ctx} @ m \quad \Gamma. \widehat{\boldsymbol{\omega}}_{\mu} \vdash A \operatorname{type}_{1} @ n}{\Gamma. (\mu \mid A) \widehat{\boldsymbol{\omega}}_{\mu} \vdash \mathbf{v}_{0} : A[\uparrow. \widehat{\boldsymbol{\omega}}_{\mu}] @ n} \quad \frac{\Gamma \operatorname{ctx} @ m}{\Gamma \vdash \operatorname{tt}, \operatorname{ff} : \mathbb{B} @ m}$$

$$\frac{\Gamma. (1 \mid \mathbb{B}) \vdash A \operatorname{type}_{1} @ m \quad \Gamma \vdash M_{t} : A[\operatorname{id}.\operatorname{tt}] @ m \quad \Gamma \vdash M_{f} : A[\operatorname{id}.\operatorname{ff}] @ m \quad \Gamma \vdash N : \mathbb{B} @ m}{\Gamma \vdash \operatorname{if}(A; M_{t}; M_{f}; N) : A[\operatorname{id}.N] @ m}$$

$$\frac{\Gamma \operatorname{ctx} @ m \quad \Gamma \vdash A \operatorname{type}_{0} @ m}{\Gamma \vdash \operatorname{Code}(A) : \cup @ m} \quad \frac{\Gamma \operatorname{ctx} @ m \quad \Gamma \vdash A \operatorname{type}_{1} @ m \quad \Gamma \vdash M : A @ m}{\Gamma \vdash \operatorname{refl}(M) : \operatorname{Id}_{A}(M, M) @ m}$$

$$\frac{\Gamma \operatorname{ctx} @ m \quad \Gamma \vdash A \operatorname{type}_{1} @ m \quad \Gamma. (1 \mid A). (1 \mid A[\uparrow]). (1 \mid \operatorname{Id}_{A[\uparrow^{2}]}(\mathbf{v}_{1}, \mathbf{v}_{0})) \vdash B \operatorname{type}_{1} @ m}{\Gamma. (1 \mid A) \vdash M : B[\uparrow. \mathbf{v}_{0}. \mathbf{v}_{0}. \operatorname{refl}(\mathbf{v}_{0})] @ m \quad \Gamma \vdash N_{0}, N_{1} : A @ m \quad \Gamma \vdash P : \operatorname{Id}_{A}(N_{0}, N_{1}) @ m} \quad \frac{\Gamma \vdash \operatorname{J}(B, M, P) : B[\operatorname{id}.N_{0}.N_{1}.P] @ m}{\Gamma \vdash \operatorname{Id}_{A}(N_{0}, N_{1}) @ m}$$

$$\frac{\Gamma \operatorname{ctx} @ m \quad \mu : \operatorname{Hom}_{\mathcal{M}}(n, m) \quad \Gamma. \widehat{\boldsymbol{\omega}}_{\mu} \vdash A \operatorname{type}_{1} @ n \quad \Gamma. \widehat{\boldsymbol{\omega}}_{\mu} \vdash M : A @ n}{\Gamma \vdash \operatorname{mod}_{\mu}(M) : \langle \mu \mid A \rangle @ m}$$

$$\frac{\nu : \operatorname{Hom}_{\mathcal{M}}(o, n)}{\mu : \operatorname{Hom}_{\mathcal{M}}(n, m) \quad \Gamma \operatorname{ctx} @ m \quad \Gamma. \widehat{\boldsymbol{\omega}}_{\mu}. \widehat{\boldsymbol{\omega}}_{\nu} \vdash A \operatorname{type}_{1} @ o \quad \Gamma. \widehat{\boldsymbol{\omega}}_{\mu} \vdash M_{0} : \langle \nu \mid A \rangle @ n} \quad \frac{\Gamma. (\mu \mid \langle \nu \mid A \rangle) \vdash B \operatorname{type}_{1} @ m \quad \Gamma. (\mu \circ \nu \mid A) \vdash M_{1} : B[\uparrow. \operatorname{mod}_{\nu}(\mathbf{v}_{0})] @ m}{\Gamma \vdash \operatorname{let}_{\mu} \operatorname{mod}_{\nu}(\_) \leftarrow M_{0} \text{ in } M_{1} : B[\operatorname{id}.M_{0}] @ m}$$

$$\frac{\Gamma \operatorname{ctx} @ m \quad \Gamma. \widehat{\boldsymbol{\omega}}_{\mu} \vdash A \operatorname{type}_{1} @ n \quad \Gamma. (\mu \mid A) \vdash B \operatorname{type}_{1} @ m \quad \Gamma. (\mu \mid A) \vdash M : B @ m}{\Gamma \vdash \lambda(M) : (\mu \mid A) \rightarrow B @ m}$$

$$\frac{\mu : \operatorname{Hom}_{\mathcal{M}}(n, m) \quad \Gamma \operatorname{ctx} @ m \quad \Gamma. \widehat{\boldsymbol{\omega}}_{\mu} \vdash A \operatorname{type}_{1} @ n}{\Gamma. (\mu \mid A) \vdash B \operatorname{type}_{1} @ m \quad \Gamma \vdash M_{0} : (\mu \mid A) \rightarrow B @ m \quad \Gamma. \widehat{\boldsymbol{\omega}}_{\mu} \vdash M_{1} : A @ n} \quad \frac{\Gamma \vdash M_{0}(M_{1}) : B[\operatorname{id}.M_{1}] @ m}{\Gamma \vdash M_{0}(M_{1}) : B[\operatorname{id}.M_{1}] @ m}$$

$$\frac{\Gamma \operatorname{ctx} @ m}{\Gamma \vdash A \operatorname{type}_{1} @ m \quad \Gamma. (1 \mid A) \vdash B \operatorname{type}_{1} @ m \quad \Gamma \vdash M_{0} : A @ m \quad \Gamma \vdash M_{1} : B[\operatorname{id}.M_{0}] @ m} \quad \frac{\Gamma \vdash (M_{0}, M_{1}) : \sum(A, B) @ m}{\Gamma \vdash (M_{0}, M_{1}) : \sum(A, B) @ m}$$

$$\frac{\Gamma \operatorname{ctx} @ m \quad \Gamma \vdash A \operatorname{type}_{1} @ m \quad \Gamma. (1 \mid A) \vdash B \operatorname{type}_{1} @ m \quad \Gamma \vdash M : \sum(A, B) @ m}{\Gamma \vdash \operatorname{pr}_{0}(M) : A @ m \quad \Gamma \vdash \operatorname{pr}_{1}(M) : B[\operatorname{id}.\operatorname{pr}_{0}(M)] @ m}$$

$$\frac{\Gamma, \Delta \operatorname{ctx} @ m \quad \Delta \vdash A \operatorname{type}_{1} @ m \quad \Gamma \vdash \delta : \Delta @ m \quad \Delta \vdash M : A @ m}{\Gamma \vdash M[\delta] : A[\delta] @ m}$$

Figure 6: MTT Terms