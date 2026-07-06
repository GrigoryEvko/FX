11:62

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

is in some ways similar to dual-context calculi, where meticulous expert attention is needed to show the admissibility of substitution in each modal setting.

The final and most serious issue with the Fitch-style is the difficulty of accounting for multiple distinct modalities. Each modality should give rise to a different lock, but the structural rules governing their interactions are complex. It is well-understood how to model the ▶ modality in a Fitch-style type theory, and [GSB19a] developed an extensive account of the □ modality. However, it is an open problem whether the two may be combined. There is work to this effect in a simple type theory [BGM19], but even in this case there are restrictions on □ and ▶ which prevent the recovery of the MLTT$_{a}$ type theory of [GSB19a] as a subsystem.

These issues seem to converge to one cause: rules that ‘remove’ elements from the context during type-checking appear difficult to manage when combining modalities. As they operate on a syntactic level, they also seem to prohibit the formulation of internal languages. Drawing on this intuition, MTT has adopted the simple introduction rules of Fitch-style calculi, but not the elimination rules. The result is a less powerful type theory, with a weaker definitional equality, and no definitional $\eta$-principle. In return, MTT scales to any mode theory, including any number of interacting modalities.

**11.4. Other work.** The question of a multimodal framework for type theory has also been tackled by other recent work [LS16, LSR17]. This line of research is commonly referred to as the *LSR* framework, after the initials of the authors. LSR is designed to handle a wide variety of modal situations in combination with a variety of different *substructural* settings. There has been ongoing work on extending this system to a full dependent type theory, but as of late 2020 this work remains unpublished.

The impetus for the LSR framework is mainly derived from a long-standing wish to address the interaction between dependent types and substructural logics. This is an axis of generalization which is entirely outside the scope of MTT. However, we may compare LSR to MTT along the modal axis.

The idea of parametrizing a type theory by a mode theory, as we have done with MTT, originates in a paper preceding the LSR framework [LS16]. In fact, the modal situations that can be handled by MTT are a strict subset of those which can be handled by pre-LSR/LSR, which also includes a modality representing the *left adjoint* as an operation on types (and not just contexts). By contrast, MTT has a simpler syntax which is amenable to current proof and implementation techniques. This is reflected in our proof of canonicity, and our experimental implementation efforts [Nuy19]. We therefore believe that MTT is a natural halfway point between current modal type theories (which are custom-fitted for each modal situation) and the full generality of LSR: it is a simpler theory which accounts for many situations of interest.

## 12. CONCLUSIONS

We introduced and studied MTT, a dependent type theory parametrized by a mode theory that describes interacting modalities. We have demonstrated that MTT may be used to reason about several important modal settings, and proven basic metatheorems about its syntax, including canonicity.

Several distinct directions of future work present themselves.