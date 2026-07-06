4

E. Cavallo and C. Sattler

In Section 4, we introduce the cube category $\square_{\vee}$ and its basic properties, construct the cubical-type model structure on $\mathrm{PSh}(\square_{\vee})$ using the results of the previous section, and define a triangulation adjunction $\mathrm{T}: \mathrm{PSh}(\square_{\vee}) \xrightarrow{\leftarrow} \mathrm{PSh}(\Delta): N_{\square}$. We moreover characterize the cube category's idempotent completion $\overline{\square}_{\vee}$. The categories of presheaves on $\square_{\vee}$ and $\overline{\square}_{\vee}$ are equivalent, but by working with the latter we can more easily compare with the simplex category, following [Sat19; SW21]. In particular we have an embedding $\blacktriangle: \Delta \to \overline{\square}_{\vee}$, thus an adjoint triple $\blacktriangle_{!} \dashv \blacktriangle^{*} \dashv \blacktriangle_{*}$ relating $\mathrm{PSh}(\Delta)$ and $\mathrm{PSh}(\overline{\square}_{\vee})$; the triangulation adjunction corresponds to $\blacktriangle^{*} \dashv \blacktriangle_{*}$ along the equivalence $\mathrm{PSh}(\square_{\vee}) \simeq \mathrm{PSh}(\overline{\square}_{\vee})$. In Section 4.4 we show that both $\blacktriangle_{!} \dashv \blacktriangle^{*}$ and $\blacktriangle^{*} \dashv \blacktriangle_{*}$ are Quillen adjunctions.

We focus on the adjunction $\blacktriangle_{!} \dashv \blacktriangle^{*}$. It is easy to see that its derived unit is valued in weak equivalences, as $\blacktriangle$ is fully faithful. To show its derived counit is valued in weak equivalences, we spend Section 5 developing a theory of relative elegance. In Section 6, we show that the functor $i: \square_{\vee} \to \mathbf{SLat}_{\mathrm{im}}^{\mathrm{inh}}$ is relatively elegant by way of a general analysis of Reedy categories of finite algebras. In Section 7 we use this result to complete the Quillen equivalence between $\widehat{\square}_{\vee}^{\mathrm{ty}}$ and $\widehat{\Delta}^{\mathrm{kq}}$. We show first that $\blacktriangle_{!} \dashv \blacktriangle^{*}$ is a Quillen equivalence, then deduce that $\blacktriangle^{*} \dashv \blacktriangle_{*}$ is one as well, concluding with our main theorem as an immediate corollary:

Theorem 7.8 The triangulation-nerve adjunction $\mathrm{T}: \widehat{\square}_{\vee}^{\mathrm{ty}} \xrightarrow{\leftarrow} \widehat{\Delta}^{\mathrm{kq}}: N_{\square}$ is a Quillen equivalence.

As a final corollary, we show in Section 7.2 that $\widehat{\square}_{\vee}^{\mathrm{ty}}$ coincides with Cisinski's test model structure on $\mathrm{PSh}(\square_{\vee})$.

In Appendix A, we give proofs of some negative results concerning Reedy structures on cartesian cube categories with connections. First, we check that neither $\square_{\vee}$ nor its idempotent completion supports a Reedy structure, justifying our recourse to relative elegance. Second, we prove that $\square_{\wedge \vee}$ does not embed elegantly in any Reedy category, showing that our techniques cannot be applied in the two-connection case.

# 1.1 Related work

# 1.1.1 Cartesian cubes

This work's closest relative is the equivariant model structure $\widehat{\square}_{\times}^{\mathrm{eq}}$ on presheaves over the cartesian cube category $\square_{\times}$ constructed by Awodey, Cavallo, Coquand, Riehl, and Sattler (ACCRS) [ACCRS24], which also classically presents $\infty$-Gpd. The ACCRS construction is a modification of earlier models in presheaves on $\square_{\times}$ [ABCHFL21; CMS20; Awo23]. Briefly, where the definition of fibration involves lifting against maps $1 \to \mathbb{I}$ from the point to the interval, the definition of equivariant fibration involves lifting against maps $1 \to \mathbb{I}^n$ for all $n$ and requires lifts stable under permutations of $\mathbb{I}^n$. Like our own model structure, $\widehat{\square}_{\times}^{\mathrm{eq}}$ is compatible with a constructive interpretation of HoTT.

In $\widehat{\square}_{\vee}^{\mathrm{ty}}$, equivariance does not appear explicitly but is still implicitly present: when the interval supports a connection operator, ordinary and equivariant lifting become interderivable (see Remark 4.25). Our model structure may thus be seen as an instance of the equivariant model structure construction applied in $\mathrm{PSh}(\square_{\vee})$, one which happens to admit a simpler description.

2025/10/16 00:43