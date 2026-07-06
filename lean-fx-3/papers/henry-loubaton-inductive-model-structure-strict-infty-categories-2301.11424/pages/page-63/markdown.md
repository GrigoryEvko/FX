**A.10 Theorem.** *If $\mathcal{C}$ is a premodel category and $R$ is a Reedy category, then $\mathcal{C}^R$ is a premodel category with the class of maps described above.*

*Furthermore, if $\mathcal{C}$ is a left semi-model category, then $\mathcal{C}^R$ is a left semi-model category with the weak equivalences being the levelwise weak equivalences.*

A more detailed treatment of Reedy model structures in the context of weak model categories, with more detailed proofs, can be found in Appendix C.2 of [8]. Though most of it is devoted to dealing with weakened assumptions regarding the existence of limits and colimits, which are not relevant in the present context.

*Proof.* The proof carries over essentially unchanged from the case of Quillen model structures. The proof that these form weak factorization systems on $\mathcal{C}^R$ as in Theorem 5.2.5 of [26] relies on the fact that we have weak factorization systems on $\mathcal{C}$ and hence carries over to the case of premodel categories. The other key argument can be found in the proof of Theorem 5.1.3 of [26] and shows that, because of the 2-out-of-3 property for weak equivalences, a Reedy fibration is a Reedy anodyne fibration if and only if it is a weak equivalence, and by the exact same argument, a Reedy cofibration with cofibrant domain is a Reedy anodyne cofibration if and only if it is a levelwise equivalence. □

A lemma that plays a significant role in this proof and that we will use at some points is:

**A.11 Lemma.** *If $R$ is a direct category (that is, a Reedy category with $R = R^+$) and $A \rightarrow B$ is a Reedy (anodyne) cofibration in $\mathcal{C}^R$, then the comparison map*

$$\operatorname{Colim}_{r \in R} A(r) \rightarrow \operatorname{Colim}_{r \in R} B(r)$$

*is an (anodyne) cofibration.*

*Proof.* This is essentially Corollary 5.1.5 of [26]. The simplest way to prove it is to observe that the colimit functor is the left adjoint to the 'constant' functor, and the constant functor clearly sends the fibrations and anodyne fibrations of $\mathcal{C}$ to Reedy fibrations and anodyne Reedy fibrations in $\mathcal{C}^R$, as Reedy fibrations for a direct category are just levelwise fibrations. □

## References

- [1] Fahd Ali Al-Agl, Ronald Brown, and Richard Steiner. Multiple categories: The equivalence of a globular and a cubical approach. *Advances in Mathematics*, 170:71–118, 2002.
- [2] Dimitri Ara. A Quillen theorem B for strict $\infty$-categories. *Journal of the London Mathematical Society*, 100(2):470–497, 2019.
- [3] Dimitri Ara. Habilitation à diriger des recherche: Théorie de l'homotopie des $\infty$-catégories strictes. 2022.
- [4] Dimitri Ara, Albert Burroni, Yves Guiraud, Philippe Malbos, François Métayer, and Samuel Mimram. Polygraphs: from rewriting to higher categories. *arXiv preprint arXiv:2312.00429*, 2023.

63