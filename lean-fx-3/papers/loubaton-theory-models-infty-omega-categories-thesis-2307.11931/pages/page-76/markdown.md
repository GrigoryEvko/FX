CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

privileged framework for stating and proving strictification results, as done in [OR20a], [GOR21], [OR22] and [Mae23]. However, they do not interact a priori well with the globular language. The goal of this chapter is to show that, with some computation, it is possible to have a globular point of view in this model.

The first section is a recollection of usual results and definitions about complicial sets. In the second section, we aim to prove an analogue of the formula given in 1.2.3.13 to the complicial setting. We also have a suspension in this category, which is denoted by $X \mapsto \Sigma X$. Objects $[1] \vee \Sigma X$ and $\Sigma X \vee [1]$ are defined in 2.2.2.19, but for now, we can suppose that they are fibrant replacements of respectively $[1] \coprod_{[0]} \Sigma X$ and $\Sigma X \coprod_{[0]} [1]$. They come along with morphisms that are analogue to whiskerings, and that we also note by $\nabla$:

$$\nabla : \Sigma X \to [1] \vee \Sigma X \quad \text{and} \quad \nabla : \Sigma X \to \Sigma X \vee [1].$$

We then show the following theorem:

**Theorem 2.3.1.1.** There exists a zigzag of acyclic cofibrations, natural in $X$, between $(\Sigma X) \otimes [1]$ and the colimit of the following diagram:

$$\Sigma X \vee [1] \xleftarrow{\nabla} \Sigma(X \otimes \{0\}) \hookrightarrow \Sigma(X \otimes [1]) \hookleftarrow \Sigma(X \otimes \{1\}) \xrightarrow{\nabla} [1] \vee \Sigma X.$$

We also provide similar formulas for the Gray cone and Gray o-cone:

**Theorem 2.3.2.1.** There exists a zigzag of acyclic cofibrations, natural in $X$, between $\Sigma X \star [0]$ and the colimit of the following diagram:

$$\Sigma X \vee [1] \leftarrow \Sigma X \to \Sigma([0] \stackrel{co}{\star} X).$$

There exists a zigzag of acyclic cofibrations, natural in $X$, between $[0] \stackrel{co}{\star} \Sigma X$ and the colimit of the following diagram:

$$\Sigma(X \star [0]) \leftarrow \Sigma X \to [1] \vee \Sigma X.$$

The third section uses this formula and the strictification result of Gagna, Ozornova and Rovelli ([GOR21]) to demonstrate a criterion for detecting autoequivalences of complicial sets by their behavior on globes. Indeed, in section 2.4, by iterating the suspension, we construct a globular object:

$$\mathbf{D}_0 \xrightarrow[i_0^-]{i_0^+} \mathbf{D}_1 \xrightarrow[i_1^-]{i_1^+} \mathbf{D}_2 \xrightarrow[i_3^-]{i_3^+} \dots$$

**Theorem 2.4.4.14.** Let $i$ be a left Quillen endofunctor for the model category for complicial sets. Suppose that there exists a zigzag of weakly invertible natural transformations:

$$i(\mathbf{D}_-) \rightsquigarrow \mathbf{D}_-.$$

Then, there exists a zigzag of weakly invertible natural transformations between $i$ and $id$.

66