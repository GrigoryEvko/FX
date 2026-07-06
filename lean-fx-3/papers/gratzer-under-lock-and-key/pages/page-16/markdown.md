**Normality** Most modal logics are single-mode, single-modal-operator logics. Following our approach in §2 we want construct a mode theory consisting of a single object $\bullet$. The axioms of 2-categories then dictate that we define a category $\mathrm{Hom}_{\mathcal{M}}(\bullet, \bullet)$ of modalities and their transformations. The *objects* of this category are the modalities, and the *morphisms* are the transformations between them. There also needs to be a composition functor

$$\circ : \mathrm{Hom}_{\mathcal{M}}(\bullet, \bullet) \times \mathrm{Hom}_{\mathcal{M}}(\bullet, \bullet) \rightarrow \mathrm{Hom}_{\mathcal{M}}(\bullet, \bullet)$$

On objects this functor maps any two modalities to their composite; on morphisms it maps two transformations of modalities to their *horizontal composite*.

Suppose that, as in §2, we define $\mathcal{M}_{\mathbf{K}}$ to be the free category on one generator, so that $\mathrm{Hom}_{\mathcal{M}}(\bullet, \bullet)$ is the *set* consisting of the modalities $\square^n : \bullet \rightarrow \bullet$ for each $n \in \mathbb{N}$. Defining $\square \varphi \stackrel{\mathrm{def}}{=} \langle \square \mid \varphi \rangle$ the proofs of Eq. (3) read

$$\begin{aligned} &\vdash \square(\varphi \rightarrow \psi) \rightarrow \square \varphi \rightarrow \square \psi \circledast m \\ &\vdash \square(\varphi \wedge \psi) \leftrightarrow \square \varphi \wedge \square \psi \circledast m \end{aligned}$$

Thus the 'simplest' mode theory $\mathcal{M}_{\mathbf{K}}$ generates a logic that is a lot like $\mathbf{K}$.

**Axioms as transformations** We will now demonstrate how the transformations of the mode theory gives rise to theorems that are usually axioms of normal modal logics.

To add axioms to the logic we can then promote the set $\mathrm{Hom}_{\mathcal{M}}(\bullet, \bullet)$ itself to be the free category on additional transformations. If we also freely add horizontal composites we get a *free 2-category*. For example, if as in §2 we generate the free 2-category on

$$4 : \square \Rightarrow \square^2$$

then we get a category with an infinite number of transformations, e.g.

$$\begin{array}{rcl} 4 & : & \square \Rightarrow \square^2 \\ 1_{\square} * 4 & : & \square^2 \Rightarrow \square^3 \\ 1_{\square} * 1_{\square} * 4 & : & \square^4 \Rightarrow \square^5 \\ & : & \end{array}$$

Axiom 4 then appears in the logic through the following proof: for any $\varphi$ wff $\circledast$,

$$\begin{array}{r} 4 : \square \Rightarrow \square^2 \\ \hline (1 \mid \langle \square \mid \varphi \rangle), (\square \mid \varphi), \widehat{\square}_{\square^2} \vdash \varphi \circledast \\ 1_1 : 1 \Rightarrow 1 \\ \hline (1 \mid \langle \square \mid \varphi \rangle), (\square \mid \varphi) \vdash \langle \square^2 \mid \varphi \rangle \circledast \\ \hline (1 \mid \langle \square \mid \varphi \rangle) \vdash \langle \square \mid \varphi \rangle \circledast \\ \hline (1 \mid \langle \square \mid \varphi \rangle) \vdash \langle \square^2 \mid \varphi \rangle \circledast \\ \hline \vdash \langle \square \mid \varphi \rangle \rightarrow \langle \square^2 \mid \varphi \rangle \circledast \end{array}$$

Similarly, we could have added an axiom

$$T : \square^1 \Rightarrow \square^0$$

16