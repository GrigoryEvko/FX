ELECTRONIC NOTES IN
THEORETICAL INFORMATICS
AND COMPUTER SCIENCE

ENTICS
HTTPS://ENTICS.EPISCIENCES.ORG

VOLUME 3
PROCEEDINGS OF
MFPS 2023

# Semantics of Multimodal Adjoint Type Theory*

Michael Shulman$^{a,1}$

$^{a}$ Department of Mathematics
University of San Diego
San Diego, CA, USA

## Abstract

We show that contrary to appearances, Multimodal Type Theory (MTT) over a 2-category $\mathcal{M}$ can be interpreted in any $\mathcal{M}$-shaped diagram of categories having, and functors preserving, $\mathcal{M}$-sized limits, without the need for extra left adjoints. This is achieved by a construction called “co-dextrification” that co-freely adds left adjoints to any such diagram, which can then be used to interpret the “context lock” functors of MTT. Furthermore, if any of the functors in the diagram have right adjoints, these can also be internalized in type theory as negative modalities in the style of FitchTT. We introduce the name Multimodal Adjoint Type Theory (MATT) for the resulting combined general modal type theory. In particular, we can interpret MATT in any finite diagram of toposes and geometric morphisms, with positive modalities for inverse image functors and negative modalities for direct image functors.

Keywords: dependent type theory, modalities, modal type theory, categorical semantics

## 1 Introduction

Modal type theories involve type-forming operations, such as the classical $\square$ (necessity) and $\diamond$ (possibility), whose introduction and elimination rules modify the accessibility of previous hypotheses. The increasing number of modal type theories has led to a need for general frameworks that can be instantiated to any new example, to avoid having to develop the metatheory of each new modal type theory from scratch.

After [26,27], each instantiation of a general modal type theory is determined by a 2-category $\mathcal{M}$, the “mode theory”. Its objects denote “modes”, its morphisms generate modal operators relating types at different modes, and its 2-cells govern their interaction. However, the “LSR” theory of [26,27] is only simply typed, its definitional equality is ill-behaved, and it uses awkward global context operations.

The more recent frameworks MTT [12] and FitchTT [11] resolve these problems: they are dependently typed, with a well-behaved definitional equality, and only ever extend the context; all indications suggest their implementability [10,40]. However, their naïve semantics requires the functors interpreting the modal operators to have additional left adjoints (“context locks”), which are not visible internally in the syntax.

We will show that this defect is, for the most part, only apparent. Namely, from any suitable $\mathcal{M}$-shaped diagram of categories, we construct a new diagram whose functors all do have left adjoints, enabling an

* This material is based upon work supported by the Air Force Office of Scientific Research under award number FA9550-21-1-0009.

$^1$ Email: shulman@sandiego.edu

PUBLISHED NOVEMBER 15, 2023

10.46298/entics.12300

PROCEEDINGS AVAILABLE ONLINE AT

HTTPS://DOI.ORG/10.46298/ENTICS.PROCEEDINGS.MFPS39

© M. SHULMAN

CREATIVE COMMONS