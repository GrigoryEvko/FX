Logical Methods in Computer Science  
Volume 20, Issue 2, 2024, pp. 16:1–16:54  
<https://lmcs.episciences.org/>

Submitted Aug. 21, 2020  
Published Jun. 19, 2024

# TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

ANDREAS NUYTS AND DOMINIQUE DEVRIESE

DistriNet, KU Leuven, Belgium

*e-mail address:* andreas.nuyts@kuleuven.be, dominique.devriese@kuleuven.be

**ABSTRACT.** Presheaf models of dependent type theory have been successfully applied to model HoTT, parametricity, and directed, guarded and nominal type theory. There has been considerable interest in internalizing aspects of these presheaf models, either to make the resulting language more expressive, or in order to carry out further reasoning internally, allowing greater abstraction and sometimes automated verification. While the constructions of presheaf models largely follow a common pattern, approaches towards internalization do not. Throughout the literature, various internal presheaf operators ($\checkmark$, $\Phi$/extent, $\Psi$/Gel, Glue, Weld, mill, the strictness axiom and locally fresh names) can be found and little is known about their relative expressiveness. Moreover, some of these require that variables whose type is a shape (representable presheaf, e.g. an interval) be used affinely.

We propose a novel type former, the transpension type, which is right adjoint to universal quantification over a shape. Its structure resembles a dependent version of the suspension type in HoTT. We give general typing rules and a presheaf semantics in terms of base category functors dubbed multipliers. Structural rules for shape variables and certain aspects of the transpension type depend on characteristics of the multiplier. We demonstrate how the transpension type and the strictness axiom can be combined to implement all and improve some of the aforementioned internalization operators (without formal claim in the case of locally fresh names).

## 1. INTRODUCTION AND RELATED WORK

**1.1. The power of presheaves.** Presheaf semantics [Hof97, HS97] are an excellent tool for modelling relational preservation properties of (dependent) type theory. They have been applied to parametricity (which is about preservation of relations) [AGJ14, BCM15, ND18a, NVD17], univalent type theory (preservation of equivalences) [BCH14, CMS20, CCHM17, Hub16, KL18, Ort18, OP18], directed type theory (preservation of morphisms), guarded type theory (preservation of the stage of advancement of computation) [BM20] and even

*Key words and phrases:* dependent type theory, presheaf models, modal type theory, homotopy type theory, parametricity, directed type theory, guarded type theory.

Andreas Nuyts holds a Postdoctoral Fellowship from the Research Foundation - Flanders (FWO; 1247922N), and carried out most of this research holding a PhD Fellowship from the Research Foundation - Flanders (FWO; 1110817N). This research was partially conducted at Vrije Universiteit Brussel and funded by the Research Foundation - Flanders (FWO; G0G0519N). This research is partially funded by the Research Fund KU Leuven.

LOGICAL METHODS  
IN COMPUTER SCIENCE

DOI:10.46298/LMCS-20(2:16)2024

© A. Nuyts and D. Devriese  
Creative Commons