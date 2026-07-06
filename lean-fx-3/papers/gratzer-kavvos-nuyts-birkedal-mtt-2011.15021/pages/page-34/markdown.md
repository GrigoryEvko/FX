11:34

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

considering $\gamma^{\blacktriangleright}$ as a proof that the predicate $\Gamma^{\blacktriangleright}$ holds at the substitution $\gamma^{\triangleleft}$. Observe that if $\gamma^{\blacktriangleright} : \Gamma_{\blacktriangleleft}^{\blacktriangleright}(\gamma^{\triangleleft})$ then $\gamma^{\triangleleft}$ must be of the form $\theta^{\triangleleft}_{\blacktriangleleft}^{\blacktriangleleft}_{\mu}$ for some $\theta^{\triangleleft} : \cdot \to \Gamma^{\triangleleft}$ with $\gamma^{\blacktriangleright} : \Gamma^{\blacktriangleright}(\theta^{\triangleleft})$.

Types over $\mathcal{C}[m]$ are given by the presheaf

$$\begin{array}{l} \mathcal{T}_{m}(\Gamma) \triangleq \{ \\ \quad A^{\triangleleft} \in \mathsf{type}_{m}^{1}(\Gamma^{\triangleleft}); \\ \quad A^{\blacktriangleright} : (\gamma^{\triangleleft} : \mathsf{sb}_{m}(\cdot, \Gamma^{\triangleleft})) \to (\gamma^{\blacktriangleright} : \Gamma^{\blacktriangleright}(\gamma^{\triangleleft})) \to \mathsf{tm}_{m}(\cdot, A^{\triangleleft}[\gamma^{\triangleleft}]) \to \mathcal{V} \\ \} \end{array}$$

Extending this presheaf with some additional data gives a presheaf of terms over $\mathcal{C}[m]$:

$$\begin{array}{l} \widetilde{\mathcal{T}}_{m}(\Gamma) \triangleq \{ \\ \quad A^{\triangleleft} \in \mathsf{type}_{m}^{1}(\Gamma^{\triangleleft}); \\ \quad A^{\blacktriangleright} : (\gamma^{\triangleleft} : \mathsf{sb}_{m}(\cdot, \Gamma^{\triangleleft})) \to (\gamma^{\blacktriangleright} : \Gamma^{\blacktriangleright}(\gamma^{\triangleleft})) \to \mathsf{tm}_{m}(\cdot, A^{\triangleleft}[\gamma^{\triangleleft}]) \to \mathcal{V} \\ \quad M^{\triangleleft} \in \mathsf{tm}_{m}(\Gamma^{\triangleleft}, A^{\triangleleft}); \\ \quad M^{\blacktriangleright} : (\gamma^{\triangleleft} : \mathsf{sb}_{m}(\cdot, \Gamma^{\triangleleft})) \to (\gamma^{\blacktriangleright} : \Gamma^{\blacktriangleright}(\gamma^{\triangleleft})) \to A^{\blacktriangleright}(\gamma^{\triangleleft}, \gamma^{\blacktriangleright}, M^{\triangleleft}[\gamma^{\triangleleft}]) \\ \} \end{array}$$

Thus, a type over $\Gamma = (\Gamma^{\triangleleft}, \varphi_{\Gamma})$ in the glued model consists of a type $\Gamma^{\triangleleft} \vdash A^{\triangleleft} \mathsf{type}_{1} \circledast m$ of MTT, along with another predicate, a family of $\mathcal{V}$-small sets, indexed over both closing substitutions $\gamma^{\triangleleft}$ that satisfy the predicate $\Gamma^{\blacktriangleright}$ and terms of type $A^{\triangleleft}[\Gamma^{\triangleleft}]$.

A term over $\Gamma$ in the glued model adds to the above a term $\Gamma^{\triangleleft} \vdash M^{\triangleleft} : A^{\triangleleft} \circledast m$ of that type, and a section $M^{\blacktriangleright}$ of the aforementioned predicate. This section produces a proof that the predicate holds at that term after we close it by applying any substitution $\gamma^{\triangleleft}$ of which the $\Gamma^{\blacktriangleright}$ holds. The reindexing action of these presheaves is defined by the action of substitution on contexts, types, and terms of MTT.

It can be shown that the projection $\tau_{m}(\Gamma) \triangleq (A^{\triangleleft}, A^{\blacktriangleright}, M^{\triangleleft}, M^{\blacktriangleright}) \mapsto (A^{\triangleleft}, A^{\blacktriangleright})$ that maps terms to types by forgetting the additional data defines a representable natural transformation in the sense of Section 5.1.2; the full proof can be found in the technical report. With respect to the connectives, we only show how to interpret the base type $\mathbb{B}$, as per Section 5.2.3. For the formation and introduction rules we define:

$$\begin{array}{l} \mathbf{Bool}^{\triangleleft} = \mathbb{B} \qquad \mathbf{Bool}^{\blacktriangleright} = \lambda \gamma^{\triangleleft}, \gamma^{\blacktriangleright}, M^{\triangleleft}. (M^{\triangleleft}[\gamma^{\triangleleft}] = \mathsf{tt}) + (M^{\triangleleft}[\gamma^{\triangleleft}] = \mathsf{ff}) \\ \mathsf{tt}^{\triangleleft} = \mathsf{tt} \qquad \mathsf{tt}^{\blacktriangleright} = \lambda_{\dots} \iota_{0}(\star) \\ \mathsf{ff}^{\triangleleft} = \mathsf{ff} \qquad \mathsf{ff}^{\blacktriangleright} = \lambda_{\dots} \iota_{1}(\star) \end{array}$$

We must now define the left lifting structure $\mathbf{if} : [\mathbf{tt}, \mathbf{ff}] \pitchfork \tau_{m}$. In type-theoretic notation:

$$\begin{array}{l} \mathbf{if}(C, [c_{0}, c_{1}], M)^{\triangleleft} = \mathbf{if}(C^{\triangleleft}; c_{0}^{\triangleleft}; c_{1}^{\triangleleft}; M^{\triangleleft}) \\ \mathbf{if}(C, [c_{0}, c_{1}], M)^{\blacktriangleright} = \lambda \gamma^{\triangleleft}, \gamma^{\blacktriangleright}. \begin{cases} c_{0}^{\blacktriangleright}(\gamma^{\triangleleft}, \gamma^{\blacktriangleright}) & \text{if } M^{\blacktriangleright}(\gamma^{\triangleleft}, \gamma^{\blacktriangleright}) = \iota_{0}(\star) \\ c_{1}^{\blacktriangleright}(\gamma^{\triangleleft}, \gamma^{\blacktriangleright}) & \text{if } M^{\blacktriangleright}(\gamma^{\triangleleft}, \gamma^{\blacktriangleright}) = \iota_{1}(\star) \end{cases} \end{array} \end{array}$$