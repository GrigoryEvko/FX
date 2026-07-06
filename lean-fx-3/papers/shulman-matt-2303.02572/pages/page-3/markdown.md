Shulman

18–3

The co-dextrification does require each $\mathcal{C}_p$ to have, and each $\mathcal{C}_\mu$ to preserve, limits of the size of $\mathcal{M}$. This is unproblematic if $\mathcal{M}$ is finite, but modal operators often come in adjoint pairs (e.g. as geometric morphisms of topoi), and as soon as $\mathcal{M}$ contains a generic adjunction it is infinite. Fortunately, if some $\mathcal{C}_\mu$ has a right adjoint, that adjoint automatically lifts to a *dependent right adjoint* of $\tilde{\mathcal{C}}_\mu$. Thus, it suffices to apply co-dextrification over a smaller 2-category $\mathcal{L}$ that generates $\mathcal{M}$ by adding some right adjoints.

The resulting type theory represents the morphisms in $\mathcal{L}$ by positive modalities as in MTT, but their right adjoints by negative modalities as in FitchTT. (For a particular $\mathcal{L}$, such a combination appeared in [5].) The positive elimination rules also restrict which morphisms of $\mathcal{M}$ can appear as “framings”: this would be problematic for internalizing functoriality, except for the stronger elimination rule of the negative modalities. We call this theory **Multimodal Adjoint Type Theory (MATT)**. If we regard $\mathcal{L}$, rather than $\mathcal{M}$, as the fundamental parameter of MATT, then it restores the symmetry of [26,27] in which each morphism (of $\mathcal{L}$) generates a positive/negative pair of modalities that are automatically adjoint.

## Acknowledgement

I am extremely grateful to Daniel Gratzer, for many long and illuminating conversations about modal type theories, for many concrete suggestions about MATT (including the name), and for careful reading and bugfixes. Dan Licata also contributed useful ideas to some of these conversations.

## 2 Multimodal Adjoint Type Theory

For a 2-category $\mathcal{M}$ we write its objects as $p, q, r, s, \dots$, its morphisms as $\mu, \nu, \varrho, \sigma, \dots$, and its 2-cells as $\alpha, \beta, \dots$. We use $\circ$ for both composition of morphisms and vertical composition of 2-cells, and write $\mu \triangleleft \beta$ and $\alpha \triangleright \nu$ for whiskering. We will not use horizontal composition of 2-cells.

Although our semantics will have a mode theory with right adjoints added freely, it is simpler to formulate syntax using an arbitrary 2-category $\mathcal{M}$ equipped with placeholders for the necessary restrictions.

**Definition 2.1** An **adjoint mode theory** is a 2-category $\mathcal{M}$ equipped with four classes of morphisms in $\mathcal{M}$ called **tangible**, **sharp**, **transparent**, and **sinister**, such that

- Every identity morphism is transparent and sharp.
- If $\mu : p \rightarrow q$ is sharp and $\nu : q \rightarrow r$ is transparent, then $\nu \circ \mu : p \rightarrow r$ is tangible. (Thus, every transparent or sharp morphism, and in particular every identity morphism, is tangible.)
- Every sinister morphism $\mu : p \rightarrow q$ has a right adjoint $\mu^\dagger : q \rightarrow p$ in $\mathcal{M}$, with unit $\eta_\mu : 1 \Rightarrow \mu^\dagger \circ \mu$ and counit $\epsilon_\mu : \mu \circ \mu^\dagger \Rightarrow 1$.

MATT over an adjoint mode theory $\mathcal{M}$ is MTT [12] over $\mathcal{M}$ with a few modifications. We write $x :^\mu A$ in place of $x : (\mu \mid A)$, and $\mu \square A$ in place of $(\mu \mid A)$. We will show the most important MTT rules, but we omit technical details of substitutions. We now list the substantive modifications.

(1) The modalities annotating variables in contexts must be tangible. Tangibility of identities yields ordinary type theories at each mode. The context rules are shown in Figure 2, along with a substitution rule that combines functoriality and naturality (the other substitution rules are more ordinary), and the variable-use rule in Figure 3 along with the rule for substituting keys into variables.²
(2) The modalities $\mu$ that annotate domains of function-types $(x :^\mu A) \rightarrow B$ must be sharp. Sharpness of identities yields ordinary function-types, and tangibility of sharp morphisms is required for the formation and introduction rules. All the rules are shown in Figure 4.
(3) The modalities $\mu$ that generate positive modal operators $\mu \square A$ must be sharp, and the “framing” modality in its elimination rule must be transparent. The rules for positive modal operators are shown in Figure 5. The elimination rule requires both transparent morphisms, and composites of transparent and sharp morphisms, to be tangible.

² The latter is not fully precise, e.g. we have not defined the “weakening” substitution $\uparrow^\alpha$. In the formal presentation of [12] there is only a zero-variable, to which can be applied substitutions involving 2-cell keys and weakening.