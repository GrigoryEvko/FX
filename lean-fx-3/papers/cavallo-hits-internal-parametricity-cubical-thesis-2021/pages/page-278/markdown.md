266

Programming in cohesive parametric type theory

Lemma 15.1.1 (Pointwise elimination). We have a term letdiscpt(d.B, P, a.N) validating the following for any Γ ≫ A type @ pt, family Γ, (dsc | d : Disc(A)) ≫ B type @ pt, and Γ, a : A ≫ N ∈ B[mod(a)/d] @ pt.

$$\frac{\Gamma.\text{dsc} \gg P \in \text{Disc}(A) \text{ @ par}}{\Gamma \gg \text{letdisc}_{\text{pt}}(d.B, P, a.N) \in B[P/d] \text{ @ pt}}$$

$$\frac{\Gamma \gg M \in A \text{ @ pt}}{\Gamma \gg \text{letdisc}_{\text{pt}}(d.B, \text{mod}(M), a.N) = N[M/a] \in B[\text{mod}(M)/d] \text{ @ pt}}$$

Proof. We define pointwise elimination as ordinary elimination into the codiscrete embedding of B.

$$\text{letdisc}_{\text{pt}}(d.B, P, a.N) := \text{unmod}(\text{letdisc}(d.\text{Codisc}(B), P, a.\text{mod}(N)))$$

We aim to show this term has type B[P/d]. By the projection rule for Codisc, it suffices to show that Γ.dsc ≫ letdisc(d.Codisc(B), P, a.mod(N)) ∈ Codisc(B[P/d]).

To show Γ.dsc, d : Disc(A) ≫ Codisc(B) type @ par, it suffices by Codisc-formation to check that (Γ.dsc, d : Disc(A)).glo ≫ B type @ pt. We have (Γ.dsc, d : Disc(A)).glo = Γ.dsc.glo, (dsc | d : Disc(A)) by definition. It follows from Γ, (dsc | d : Disc(A)) ≫ B type @ pt and the counit substitution of the discrete-global adjunction that we have Γ.dsc.glo, (dsc | d : Disc(A)) ≫ B type @ pt.

To show Γ.dsc, (cc | a : A) ≫ mod(N) ∈ Codisc(B[mod(a)/d]) @ par, it suffices by Codisc-introduction to show (Γ.dsc, (cc | a : A)).glo ≫ N ∈ B[mod(a)/d] @ pt. Again we compute the action of context modality.

$$(\Gamma.\text{dsc}, (cc \mid a : A)).\text{glo} = \Gamma.\text{dsc.glo}, (\text{dsc}, cc \mid a : A)$$

We deduce Γ.dsc.glo, (dsc, cc | a : A) ≫ N ∈ B[mod(a)/d] @ pt from the assumption Γ, a : A ≫ N ∈ B[mod(a)/d] @ pt using the counit substitution of the discrete-global adjunction and the unit of the components-discrete adjunction.

Combining these with Γ.dsc ≫ P ∈ Disc(A) @ par, we apply parametric elimination to see that Γ.dsc ≫ letdisc(d.Codisc(B), P, a.mod(N)) ∈ Codisc(B[P/d]) @ par. The projection rule for the codiscrete type now gives the conclusion of the first rule. The second rule follows analogously by the reduction rules for the discrete eliminator and codiscrete projection. □

In truth, we will use this elimination principle only to define the following construction for projecting the underlying element of A from a hypothesis (dsc | d : Disc(A)).

Lemma 15.1.2. Given A type and (dsc | d : Disc(A)), there is some undisc(d) ∈ A with the following properties.