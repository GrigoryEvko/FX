CONTENTS

**Theorem 1.2.4.14.** *There is a natural identification between $1 \stackrel{co}{\star} [A, 1]$ and the colimit of the following diagram*

$$[1] \vee [A, 1] \xleftarrow{\nabla} [A, 1] \longrightarrow [A \star 1, 1]$$

*There is a natural identification between $[A, 1] \star 1$ and the colimit of the following diagram*

$$[1 \stackrel{co}{\star} A, 1] \longleftarrow [A, 1] \xrightarrow{\nabla} [A, 1] \vee [1]$$

*There is a natural identification between $1 \star [A, 1]$ and the colimit of the following diagram.*

$$[1 \star A, 1] \longleftarrow [A, 1] \xrightarrow{\nabla} [1] \vee [A, 1]$$

**Chapter 2.** This chapter is dedicated to the study of *Verity complicial sets*, defined and extensively studied by Verity ([Ver08c])

One of the benefits of complicial sets is that they admit a simple definition of the Gray tensor product. Being strongly linked to $(0, \omega)$-categories by the Street nerve, they are also a privileged framework for stating and proving strictification results, as done in [OR20a], [GOR21], [OR22] and [Mae23]. However, they do not interact *a priori* well with the globular language. The goal of this chapter is to show that, with some computation, it is possible to have a globular point of view on theses objects.

The first section is a recollection of usual results and definitions about complicial sets. In the second section, we aim to prove an analogue of the formula given in 1.2.4.13 to the complicial setting. We also have a suspension in this category, which is denoted by $X \mapsto \Sigma X$. Objects $[1] \vee \Sigma X$ and $\Sigma X \vee [1]$ are defined in 2.2.2.18, but for now, we can suppose that they are fibrant replacements of respectively $[1] \coprod_{[0]} \Sigma X$ and $\Sigma X \coprod_{[0]} [1]$. They come along with morphisms that are analogue to whiskerings, and that we also note by $\nabla$:

$$\nabla : \Sigma X \to [1] \vee \Sigma X \quad \text{and} \quad \nabla : \Sigma X \to \Sigma X \vee [1].$$

We then show the following theorem:

**Theorem 2.3.1.1.** *There exists a zigzag of acyclic cofibrations, natural in $X$, between $(\Sigma X) \otimes [1]$ and the colimit of the following diagram:*

$$\Sigma X \vee [1] \xleftarrow{\nabla} \Sigma(X \otimes \{0\}) \hookrightarrow \Sigma(X \otimes [1]) \leftarrow \Sigma(X \otimes \{1\}) \xrightarrow{\nabla} [1] \vee \Sigma X.$$

We also provide similar formulas for the *Gray cone* and Gray $\circ$-*cone*:

**Theorem 2.3.2.1.** *There exists a zigzag of acyclic cofibrations, natural in $X$, between $\Sigma X \star [0]$ and the colimit of the following diagram:*

$$\Sigma X \vee [1] \leftarrow \Sigma X \to \Sigma([0] \stackrel{co}{\star} X).$$

*There exists a zigzag of acyclic cofibrations, natural in $X$, between $[0] \stackrel{co}{\star} \Sigma X$ and the colimit of the following diagram:*

$$\Sigma(X \star [0]) \leftarrow \Sigma X \to [1] \vee \Sigma X.$$

The third section uses this formula and the strictification result of Gagna, Ozornova and Rovelli ([GOR21]) to demonstrate a criterion for detecting autoequivalences of complicial sets by their behavior on globes. Indeed, in section 2.4, by iterating the suspension, we construct a globular object:

$$\mathbf{D}_0 \xrightarrow[\iota_0^-]{i_0^+} \mathbf{D}_1 \xrightarrow[\iota_1^-]{i_1^+} \mathbf{D}_2 \xrightarrow[\iota_2^-]{i_2^+} \dots$$

8