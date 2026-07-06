Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:49

and the cut rules multifurcate further into:

$$\frac{\Theta' \mid \Gamma' \vdash \Delta', A \mid \Upsilon' \quad \Theta \mid \Gamma, A \vdash \Delta \mid \Upsilon}{\Theta, \Theta' \mid \Gamma, \Gamma' \vdash \Delta, \Delta' \mid \Upsilon, \Upsilon'}$$

$$\frac{\Theta' \mid \cdot \vdash A \mid \Upsilon' \quad \Theta, A \mid \Gamma \vdash \Delta \mid \Upsilon}{\Theta, \Theta' \mid \Gamma \vdash \Delta \mid \Upsilon, \Upsilon'} \quad \frac{\Theta' \mid A \vdash \cdot \mid \Upsilon' \quad \Theta \mid \Gamma \vdash \Delta \mid \Upsilon, A}{\Theta, \Theta' \mid \Gamma \vdash \Delta \mid \Upsilon, \Upsilon'}.$$

These are all precisely the relevant logical and structural rules of [Gir93].

## 9. ADJUNCTIONS INDUCED BY DOCTRINE MAPS

Our last goal is to show that a doctrine map $\mathfrak{F}: \mathbb{D}_1 \to \mathbb{D}_2$ induces a pseudo 2-adjunction relating $\mathbb{D}_1$-categories to $\mathbb{D}_2$-categories, combining the adjunctions from Proposition 5.8 and Theorem 7.4.

**Theorem 9.1.** *For any morphism $\mathfrak{F}: \mathbb{D}_1 \to \mathbb{D}_2$ of small doctrines, there is an induced pseudo 2-adjunction*

$$\widehat{\mathfrak{F}}_*: \mathbb{D}_1\text{-Cat}_g \rightleftarrows \mathbb{D}_2\text{-Cat}_g: \widehat{\mathfrak{F}}^*.$$

*Proof.* Identifying $\mathbb{D}_i$-categories with $\mathbb{D}_i$-complete sketches, we define $\widehat{\mathfrak{F}}^*$ to be the $\mathfrak{F}^*$ from Proposition 5.8 restricted to $\mathbb{D}_2$-complete inputs. This takes values in $\mathbb{D}_1$-complete sketches because the $\mathfrak{F}_*$ from Proposition 5.8 maps $\mathcal{I}_{\mathbb{D}_1}$ into $\mathcal{I}_{\mathbb{D}_2}$, up to isomorphism. Now we can define $\widehat{\mathfrak{F}}_*(\mathcal{S}) = (\widehat{\mathfrak{F}_*\mathcal{S}})_{\mathbb{D}_2}$, and compute

$$\begin{aligned} \mathbb{D}_2\text{-Cat}_g(\widehat{\mathfrak{F}}_*(\mathcal{S}), \mathcal{T}) &= \mathbb{D}_2\text{-Cat}_g(\widehat{(\mathfrak{F}_*\mathcal{S})}_{\mathbb{D}_2}, \mathcal{T}) \simeq \mathbb{D}_2\text{-Sketch}_g(\mathfrak{F}_*\mathcal{S}, \mathcal{T}) \\ &\cong \mathbb{D}_1\text{-Sketch}_g(\mathcal{S}, \mathfrak{F}^*\mathcal{T}) \cong \mathbb{D}_1\text{-Cat}_g(\mathcal{S}, \widehat{\mathfrak{F}}^*\mathcal{T}). \end{aligned}$$

**Theorem 9.2.** *For any sorted map $\mathfrak{F}: \mathbb{D}_1 \to \mathbb{D}_2$ of small sorted doctrines, there is an induced pseudo 2-adjunction*

$$\widetilde{\mathfrak{F}}_*: \mathbb{D}_1\text{-sCat}_g \rightleftarrows \mathbb{D}_2\text{-sCat}_g: \widetilde{\mathfrak{F}}^*.$$

*Proof.* It suffices to show that both functors in Theorem 9.1 preserve well-sortedness. For $\widehat{\mathfrak{F}}^* = \mathfrak{F}^*$ this follows from Proposition 6.14. For $\widehat{\mathfrak{F}}_*$, let $\mathcal{S}$ be a well-sorted $\mathbb{D}_1$-complete sketch. By Proposition 6.14, $\mathfrak{F}_*(\mathcal{S})$ is a well-sorted (incomplete) $\mathbb{D}_2$-sketch; thus by Proposition 7.5, $\widehat{\mathfrak{F}}_*(\mathcal{S}) = (\widehat{\mathfrak{F}_*\mathcal{S}})_{\mathbb{D}_2}$ is also well-sorted.

**Remark 9.3.** If $\mathbb{D}_2$ (hence also $\mathbb{D}_1$) contains only "totally covariant" operations, then Theorems 9.1 and 9.2 extend to pseudo 2-adjunctions $\mathbb{D}_1\text{-Cat} \rightleftarrows \mathbb{D}_2\text{-Cat}$ and $\mathbb{D}_1\text{-sCat} \rightleftarrows \mathbb{D}_2\text{-sCat}$ including the noninvertible 2-cells.

We conclude with examples. In fact, nearly all the obvious forgetful functors between classes of LNL polycategories discussed in Section 3 are of the form $\widehat{\mathfrak{F}}^*$ for some (sorted) doctrine map $\mathfrak{F}$, and therefore have left pseudo-adjoints.

To start with, we consider maps between doctrines that have no cones. These induce $\widehat{\mathfrak{F}}^*$ functors including the following.

- The underlying LNL multicategory of an LNL polycategory.
- The underlying cartesian multicategory, and the underlying symmetric polycategory, of an LNL multicategory or LNL polycategory.