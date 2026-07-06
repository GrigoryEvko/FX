parametrically in a specification of the modalities and their interrelations, which is called the *mode theory*.

Moreover, this new logic is not just *multimodal*—in that it sports multiple modalities—but also *multimode*. This is a new concept in modal logic. Traditionally, a modal operator $\square$ is an operator that takes a formula $\varphi$ to a formula $\square\varphi$. Crucially, the formula $\square\varphi$ is in the same syntactic category as $\varphi$. The logic in this paper will conceive of modal operators as transporting formulas *between* multiple syntactic categories. We will call these syntactic categories *modes*, and modalities will map formulas of one mode to formulas in another. Modes can be conceived of as ‘possible universes of discourse’ in which we can make various logical statements. Modalities will then allow formulas in one mode to appear in another—not directly, but as spectres under a modality. All the modal operators in the logic will preserve conjunction. Thus, their essence is one of a *necessity* modality. Extending the present approach to possibility-like modalities is an open problem.

Instead of originating from a Kripke semantics of computational interest, our logic comes from categorical logic. In fact, it is the logical isolate of a multimodal Martin-Löf Type Theory [NPS90] called MTT [Gra+20; Gra+21]. Hence, it is presented as a proof system in the style of Gentzen’s *natural deduction* [Pra65; Pra06]. Due to a lack of a double-negation elimination rule the resultant logic is intuitionistic. The formulation of a classical version of this logic as well as an associated Kripke semantics for this remains an open problem.

## 2. MODE THEORIES

### 2.1. Modes

To begin presenting the logic we must presuppose a set $\mathcal{M}$ of *modes*, with typical members $m, n, \dots \in \mathcal{M}$. Each of these modes corresponds to a syntactic category, thus partitioning the formulas of the logic. We will write

$$\varphi \circledcirc m$$

to mean that $\varphi$ is a formula at mode $m$.

### 2.2. Modalities

Modalities are traditionally endoöperators of the logic: a modality $\square$ maps a formula $\varphi \circledcirc m$ to a formula $\square\varphi \circledcirc m$ at the same mode. Our logic breaks with tradition by featuring modalities which map formulas to different modes. Thus, a modality indexed by $\mu$ applied to a formula $\varphi \circledcirc n$ at mode $n$ may yield a formula $\square_\mu\varphi \circledcirc m$ at some other mode $m$. We will also break with tradition by writing $\langle \mu \mid \varphi \rangle$ for the application of the modality indexed by $\mu$ to $\varphi$, instead of the more common notation $\square_\mu\varphi$.

We will specify the fact that $\varphi \circledcirc n$ implies $\langle \mu \mid \varphi \rangle \circledcirc m$ by writing

$$\mu : n \rightarrow m$$

2