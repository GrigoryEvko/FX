Iterated smash products

275

We then transpose to define $G \in \text{Disc}(A_* \wedge B_*) \to \text{Disc}_*(A_*) \wedge \text{Disc}_*(B_*)$ @ par as follows.

$$G := \lambda w. \left[ \begin{array}{l} \text{case } w \text{ of} \\ | \text{mod}(s) \mapsto \text{unmod}(G' s) \end{array} \right]$$

We leave detailed proofs of the inverse conditions as an exercise to the reader. The proofs predictably follow the structure of the functions themselves. Briefly, to define a map

$$(s : \text{Disc}_*(A_*) \wedge \text{Disc}_*(B_*)) \to \text{Path}(\text{Disc}_*(A_*) \wedge \text{Disc}_*(B_*), G(Fs), s)$$

we use smash product induction followed by discrete induction in each case; to show

$$(w : \text{Disc}(A_* \wedge B_*)) \to \text{Path}(\text{Disc}(A_* \wedge B_*), F(Gw), w)$$

we first prove

$$(s : A_* \wedge B_*) \to \text{Glo}(\text{Path}(\text{Disc}(A_* \wedge B_*), F(\text{unmod}(G' s)), \text{mod}(s)))$$

by smash product induction and then transpose.

□

**Commutativity** For our first concrete application, we show that any parametric commutator that behaves correctly on Bool induces a pointwise commutator that is an isomorphism.

**Assumption 15.4.6.** We assume given a global commutator as follows.

$$\text{comm} \in \text{Glo}((A_*, B_* : \mathsf{U}_*) \to A_* \wedge_* B_* \to B_* \wedge_* A_*) \text{ @ pt}$$

We assume moreover that this term satisfies the following path equality.

$$\text{comm Bool}_* \text{Bool}_* \langle\langle \text{ff}, \text{ff} \rangle\rangle \rightsquigarrow \langle\langle \text{ff}, \text{ff} \rangle\rangle$$

We derive a pointwise commutator by instantiating comm at discrete types and then applying $\blacklozenge_*$, using also that $\wedge$ commutes with Disc.

**Definition 15.4.7 (Commutator shadow).** Given pointwise types $A_*, B_* : \mathsf{U}_*$, we define $\text{comm}_{\text{pt}} A_* B_* \in A_* \wedge_* B_* \to B_* \wedge_* A_*$ @ pt as follows.

$$\text{comm}_{\text{pt}} A_* B_* := \blacklozenge_*(\text{mod}(\wedge\text{-disc } \circ_* (\text{unmod(comm)} \triangleleft A_* \triangleleft B_*) \circ_* \wedge\text{-disc}^{-1}))$$