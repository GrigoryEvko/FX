284 Formalism

**Endpoints and interval** The bridge endpoint object is populated with the two endpoints, and is included in the bridge interval by way of a “boundary” substitution $\partial$.

$$\frac{\Gamma \vdash \mathbf{0}_2 : \Gamma.2 \text{ @ } m}{\Gamma \vdash \mathbf{1}_2 : \Gamma.2 \text{ @ } m} \quad \frac{\Gamma \text{ ctx @ par}}{\Gamma.2 \vdash \partial : \Gamma.\mathbf{I} \text{ @ par}}$$

We express the interaction between the interval and action of modalities by a series of isomorphisms (up to judgmental equality) corresponding to clauses of Figure 14.1. (While these isomorphisms are equalities in the computational interpretation, we do not expect this to be the case in all models.) For example, endpoint hypotheses (and path interval hypotheses) commute with all modalities, while cc collapses interval hypotheses and glo turns them into endpoint hypotheses.

$$\frac{\Gamma \text{ ctx @ } n \quad \mu : m \rightarrow n}{\Gamma.2.\mu \vdash \text{ex}_{\mu 2} : \Gamma.\mu.2 \text{ @ } m} \quad \frac{\Gamma \text{ ctx @ } n \quad \mu : m \rightarrow n}{\Gamma.\mu.2 \vdash \text{ex}_{2\mu} : \Gamma.2.\mu \text{ @ } m}$$
$$\frac{\Gamma \text{ ctx @ par}}{\Gamma.cc \vdash cc_1 : \Gamma.\mathbf{I.cc} \text{ @ pt}} \quad \frac{\Gamma \text{ ctx @ par}}{\Gamma.\mathbf{I.glo} \vdash glo_1 : \Gamma.glo.2 \text{ @ pt}}$$

We ask that the two exchange substitutions $\text{ex}_{\mu 2}$ and $\text{ex}_{\mu 2}$ are mutually inverse (as are their equivalents for paths) and that $cc_1$ and $glo_1$ invert the substitutions $p_1 \otimes cc$ and $(\partial \otimes glo) \circ \text{ex}_{2glo}$ respectively. We also ask each substitution to be natural in $\Gamma$ and $\mu$ if applicable and interact correctly with interval-related substitutions; for example, we should have $\Gamma.\mu \vdash \text{ex}_{\mu 2} \circ (\mathbf{0}_2 \otimes \mu) = \mathbf{0}_2 : \Gamma.\mu.2 \text{ @ } m$.

We do *not* impose any additional substitutions specifying the action of the modalities on term hypotheses. It already follows from the existing rules for modalities and term hypotheses that we have the following isomorphisms.

$$\begin{aligned} &\Gamma.(\mu \mid A).\text{dsc} \cong \Gamma.\text{dsc.}(\text{cc} \otimes \mu \mid A[\{\text{cou}\} \otimes \mu]) \\ &\Gamma.(\mu \mid A).\text{glo} \cong \Gamma.\text{glo.}(\text{dsc} \otimes \mu \mid A[\{\text{cou}\} \otimes \mu]) \\ &\Gamma.(\text{cc} \otimes \mu \mid A).\text{cc} \cong \Gamma.\text{cc.}(\mu \mid A) \end{aligned}$$

That cc completely removes hypotheses not typed under cc, meanwhile, is not something we want to require in all models (and indeed fails in the cubical set model described below).

**Negative modal types** The two negative modal types—Glo and Codisc—are specified by rules following those we proved in Section 14.4.1. We show the rules for the global type here, and leave it to the reader to infer the rules for the codiscrete type. With substitutions now explicit, we see how the reduction and uniqueness equations involve the unit and