# Chapter 7

## Conclusions

### 7.1 Related work

*HITs for ITT* Higher inductive types were introduced in the context of univalent intensional type theory at the 2011 Oberwolfach meeting, in discussions between Andrej Bauer, Peter Lumsdaine, Mike Shulman, and Michael Warren (see [Uni13, §6 Notes]). The **HoTT** Book presents many examples of higher inductive types and sketches criteria for a general definition, but definite syntax and semantics for higher inductive types has since taken time to mature. In this and future extensions of **ITT** with higher inductive types, “path” constructors are expressed with identity types. Notably, the reduction rules for eliminators on path constructors are posited only up to identities, not up to exact equality, as such exact equations typically fail to hold in models. In particular, there are many identified-but-not-equal ways to define the action of an eliminator on an identity, and it is not clear that any one deserves to be designated canonical and made to satisfy an exact reduction rule.

There is one obvious and extremely simple schema: include only the quotient type $A \parallel R$ introduced in Section 5.1 (or the inter-derivable pushout). From this minimal base, it is actually possible to build out a number of more sophisticated HITs. Van Doorn [Doo16] and Kraus [Kra16] each give constructions of the propositional truncation using only the quotient, obtaining the truncation as the homotopy colimit of an $\omega$-indexed sequence of types. (Colimits indexed by $\omega$ can be defined using quotients and a natural numbers type.) Rijke [Rij17] generalized the latter to construct general $n$-truncations. While these results are theoretically valuable, the complexity of the definitions makes them unwieldy for computational purposes. Moreover, there are limits to this approach: Lumsdaine and Shulman give an example of a HIT which cannot be constructed from pushouts and the natural numbers [LS20, §9].

Moving up a degree of (a priori) expressivity, Sojakova [Soj14; Soj15; Soj16] intro-

151