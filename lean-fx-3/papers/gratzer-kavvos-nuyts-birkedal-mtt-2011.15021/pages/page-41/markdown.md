Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:41

Context structure. We define a strict 2-functor $[[-]: \mathcal{I}^{\text{coop}} \to \text{Cat}$ by

$$\begin{array}{l} i \quad \longmapsto \mathcal{C}[i] \triangleq \mathbf{PSh}(J(i)) \\ f: i \to j \longmapsto [\widehat{\mathbf{B}}_f] \triangleq J(f)^*: \mathbf{PSh}(J(j)) \to \mathbf{PSh}(J(i)) \\ \alpha: f \Rightarrow g \longmapsto [\widehat{\mathbf{q}}^\alpha] \triangleq J(\alpha)^*: J(g)^* \Rightarrow J(f)^* \end{array}$$

The variance is correct: recall that precomposition is a strict 2-functor

$$(-)^*: \mathbf{Cat}^{\text{coop}} \to \mathbf{Cat}$$

which maps a functor $f: \mathcal{C} \to \mathcal{D}$ to $f^*: \mathbf{PSh}(\mathcal{D}) \to \mathbf{PSh}(\mathcal{C})$, and a natural transformation $\alpha: f \Rightarrow g$ to $\alpha^*: g^* \Rightarrow f^*$, given by $\alpha^*_{P,c} \triangleq P(\alpha_c): P(g(c)) \to P(f(c))$. 2-functoriality is immediate, as for example $J(f)^* \circ J(g)^* = (J(g) \circ J(f))^* = J(g \circ f)^*$.

Modal natural models. To interpret the 'mode-local' structure we must construct a modal natural model in each $\mathcal{C}[i]$. It is well-known that every presheaf topos $\mathbf{PSh}(\mathcal{C})$ gives rise to a rich model of MLTT: see e.g. [Hof97, §4.1] or [Coq13].

Contexts are interpreted as objects of the presheaf category $\mathbf{PSh}(\mathcal{C})$. Types are presheaves $\mathbf{PSh}(\int \Gamma)$ over the category of elements $\int \Gamma$ of a context $\Gamma: \mathbf{PSh}(\mathcal{C})$. We define the action of a substitution $\sigma: \Delta \Rightarrow \Gamma$ on a type $A: \mathbf{PSh}(\int \Gamma)$ by

$$A[\sigma] \triangleq (\int \Delta)^{\text{op}} \xrightarrow{(\int \sigma)^{\text{op}}} (\int \Gamma)^{\text{op}} \xrightarrow{A} \mathbf{Set}$$

This is functorial because $\int -: \mathbf{PSh}(\mathcal{C}) \to \mathbf{Cat}$ and $-^{\text{op}}: \mathbf{Cat} \to \mathbf{Cat}$ are.

A term of type $A$ is a global section of $A$, i.e. a morphism $\text{Hom}_{\mathbf{PSh}(\int \Gamma)}(1, A)$. We define the action of a substitution $\sigma: \Delta \Rightarrow \Gamma$ on a term $M: \text{Hom}(1, A)$ by whiskering:

$$M[\sigma] \triangleq M * (\int \sigma)^{\text{op}}: 1 \circ (\int \sigma)^{\text{op}} \Rightarrow A \circ (\int \sigma)^{\text{op}} = A[\sigma]$$

As $1 \circ \int \sigma^{\text{op}} = 1$, this has the right type. It is functorial because whiskering is.

Remark 8.1 (Size Issues). One cannot be too careful with size issues when considering presheaf models. In Section 5.2 we demanded that the category of contexts be small, so that we can then formulate a large category of models. $\mathbf{PSh}(\mathcal{C})$ is certainly not small. We can mend this by assuming a Grothendieck universe $\mathcal{V}$ large enough to contain $\mathcal{C}$ in the ambient set theory, and re-defining $\mathbf{PSh}(\mathcal{C})$ to consist of the presheaves $P: \mathcal{C}^{\text{op}} \to \mathcal{V}$ with small fibers. As $\mathcal{V}$ is closed under all set-theoretic operations, this is still a model, and $\mathbf{PSh}(\mathcal{C})$ is small.

To interpret universes we need to know that the fibers of types in $\mathbf{PSh}(\int \mathcal{C})$ are even smaller. Thus, we further assume a second, inner Grothendieck universe $\mathcal{V}' \subset \mathcal{V}$. To a type theorist, this is just the standard technique of 'bumping' a universe level.

Connectives. Presheaf models support dependent sums and products, and extensional identity types (and therefore intensional identity types): see [Hof97, §4.2]. On the premise that the underlying set theory has a set-theoretic universe, they also support a universe, through a construction of [HS97]. See also [Coq13].

There is an equivalence $\mathbf{PSh}(\int \Gamma) \simeq \mathbf{PSh}(\mathcal{C})/\Gamma$ which shows that types are families $P \Rightarrow \Gamma$ in the slice category. However, using the latter definition would lead to strictness issues.