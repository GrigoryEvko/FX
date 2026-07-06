11:32

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

will contain a syntactic component (resp. a context, type, or term), along with a proof-relevant predicate that is appropriately fibred over it. The base types of this model are carefully chosen so that a normal form can be extracted from proofs of the predicate. By interpreting a term of ground type in the glued model we automatically obtain a proof of the predicate, from which we extract a normal form.

Such proofs involve two steps: defining the glued construction, and proving that it is a model. While the first step is often straightforward, the second usually involves checking innumerable equations. In order to shorten the proof sketched here we will make a simplifying assumption (effectively adding an equation to the algebraic syntax): we will assume that locks preserve the empty context, i.e. that

$$\cdot \widehat{\mathbf{\Omega}}_{\mu} = \cdot \mathsf{ctx} @ m$$

for $\mu : \operatorname{Hom}_{\mathcal{M}}(m, n)$. Using the universal property of the terminal context, this implies

$$\cdot \widehat{\mathbf{\Omega}}_{\mu} \vdash \mathbf{Q}^{\alpha} = \cdot = \mathsf{id} : \cdot \widehat{\mathbf{\Omega}}_{\mu} @ m \tag{6.1}$$

Requiring this equation unfortunately limits our class of models to those where the left adjoint strictly preserves the terminal product. Despite this simplification the proof remains rather long, so we will only sketch the construction of the modal natural models. The missing details may be found in an accompanying technical report.

**Remark 6.2.** In what follows we will assume the existence of two Grothendieck universes $\mathcal{V}' \subset \mathcal{V} : \mathbf{Set}$. We could make do with just one but at the price of some contortions, which are both unnecessary and tiresome. We will assume that the sets of contexts, substitutions, types, and terms of the syntactic model are $\mathcal{V}'$-small.

### 6.1. The Glued Model. We begin by defining the context structure.

**Definition 6.3** (Glued Contexts). A glued context $\Gamma$ at mode $m$ consists of a context $\Gamma^{\triangleleft} \in \mathsf{ctx}_m$, a predicate $\Gamma^{\blacktriangleright} \in \mathcal{V}$, and a function

$$\phi_{\Gamma} : \Gamma^{\blacktriangleright} \to \mathsf{sb}_m(\cdot, \Gamma^{\triangleleft})$$

A glued context $\Gamma = (\Gamma^{\triangleleft}, \Gamma^{\blacktriangleright})$ can be thought of as a proof-relevant predicate over substitutions into the syntactic context $\Gamma^{\triangleleft}$. An element $x \in \Gamma^{\blacktriangleright}$ can be thought of as a proof that the predicate holds of the substitution $\phi_{\Gamma}(x) : \cdot \to \Gamma^{\triangleleft}$. We will henceforth use the metavariable $\Gamma$ to range over glued contexts, and denote contexts of the syntax by $\Gamma^{\triangleleft}$.

**Definition 6.4** (Glued Substitutions). A glued substitution from $\Delta$ to $\Gamma$ at mode $m$ is a pair of a substitution $\gamma^{\triangleleft} \in \mathsf{sb}_m(\Delta^{\triangleleft}, \Gamma^{\triangleleft})$ and a function $\gamma^{\blacktriangleright} : \Delta^{\blacktriangleright} \to \Gamma^{\blacktriangleright}$ such that

$$\forall x \in \Delta^{\blacktriangleright} \cdot \phi_{\Gamma}(\gamma^{\blacktriangleright}(x)) = \gamma^{\triangleleft} \circ \phi_{\Delta}(x) : \cdot \to \Gamma^{\triangleleft}$$

Glued contexts and glued substitutions form a category, viz. the comma category

$$\mathcal{C}[m] \triangleq (1_{\mathcal{V}} \downarrow \mathsf{sb}_m(\cdot, -))$$

which we take as the category of contexts at mode $m$. Next, we define a 2-functor from $\mathcal{M}$ sending each $m$ to $\mathcal{C}[m]$. For each $\mu : \operatorname{Hom}_{\mathcal{M}}(m, n)$ a functor $[\widehat{\mathbf{\Omega}}_{\mu}] : \mathcal{C}[n] \to \mathcal{C}[m]$ as by