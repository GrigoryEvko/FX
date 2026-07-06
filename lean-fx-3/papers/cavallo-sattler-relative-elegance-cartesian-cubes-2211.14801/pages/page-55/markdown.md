Relative Elegance and Cartesian Cubes with One Connection

55

$\overline{\square}_{\vee} \to \mathbf{SLat}_{\mathrm{fin}}^{\perp}$ is also relatively elegant. This embedding gives a more parsimonious set of generators, but $\mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}}$ suffices for our purposes.

## 7 Equivalences and equalities

### 7.1 Equivalence with the Kan–Quillen model structure

Returning to the candidate Quillen equivalence $\blacktriangle_{!} \dashv \blacktriangle^{*}$, it remains to show that its counit is valued in weak equivalences. We first note that the collection of those $X \in \mathrm{PSh}(\overline{\square}_{\vee})$ for which $\varepsilon_{X}: \blacktriangle_{!} \blacktriangle^{*} X \to X$ is a weak equivalence is saturated by monomorphisms.

Proposition 7.1 (Cis06, Remarque 1.1.13) Let $F: \mathbf{E} \to \mathbf{F}$ be a mono- and colimit-preserving functor between cocomplete categories. If $\mathcal{P} \subseteq \mathbf{F}$ is saturated by monos, then the class $F^{-1}(\mathcal{P})$ of objects whose image by $F$ is in $\mathcal{P}$ is saturated by monos.

Proposition 7.2 If $\mathbf{M}$ has monos as cofibrations, then its class of weak equivalences is saturated by monos as a class of objects of $\mathbf{M}^{\rightarrow}$.

Proof This is proven by Cisinski [Cis06, Remarque 1.4.16] for localizers [Cis06, Définition 1.4.1]; the class of weak equivalences in a model category with monos as cofibrations is always a localizer.

Corollary 7.3 Let $\mathbf{E}$ be a cocomplete category, $\mathbf{N}$ be a model category with monos as cofibrations, and $F, G: \mathbf{E} \to \mathbf{N}$ be mono- and colimit-preserving functors. For any natural transformation $h: F \to G$, the class of objects $X \in \mathbf{E}$ such that $h_{X}: FX \to GX$ is a weak equivalence is saturated by monos.

Proof By Propositions 7.1 and 7.2, regarding $h$ as a functor $\mathbf{E} \to \mathbf{N}^{\rightarrow}$.

In particular, any natural transformation $h: F \to G$ of left Quillen adjoints $F, G: \mathbf{M} \to \mathbf{N}$ between model categories with monos as cofibrations satisfies the hypotheses of Corollary 7.3. In light of this, we only need to check that $\varepsilon$ is a weak equivalence at generating presheaves.

Lemma 7.4 Let $A \in \mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}}$ and $H \leq \operatorname{Aut}_{\mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}}}(A)$ be given. Then $N_{i}A / N_{i}H$ is weakly contractible.

Proof Per Corollary 4.51, it suffices to show that this object is a homotopy retract of 1. We have a semilattice morphism $\uparrow: [1] \times A \to A$ sending $(0, a) \mapsto a$ and $(1, a) \mapsto \top$.

2025/10/16 00:43