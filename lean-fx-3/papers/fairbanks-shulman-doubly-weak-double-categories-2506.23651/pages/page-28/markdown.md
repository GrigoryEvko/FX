28

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

composition structure. And since **2-Cptd** is a presheaf category and this chain consists of monomorphisms, its colimit in **2-Cptd** is its “union” in a straightforward sense, giving the explicit description as stated in the proposition. Finally, it is straightforward to check that $\mathbf{X}_{\infty}$ is represented, and that any map from $\mathbf{X}$ to a represented implicit 2-category factors uniquely through $\mathbf{X}_{\infty}$. $\square$

**Corollary 5.7.** *The free bicategory on a 2-computad $\mathbf{X}$ has 1-cells freely generated from those of $\mathbf{X}$ by binary composition and identities, and 2-cells as in the free strict 2-category with boundary given by erasing parentheses and identities. Similarly, the free doubly weak double category on a double computad $\mathbf{X}$ has 1-cells of both types freely generated from those of $\mathbf{X}$ by binary composition and identities, and 2-cells as in the free strict double category with boundary given by erasing parentheses and identities.*

*Proof.* Combine Proposition 5.6 and Remark 5.3. $\square$

Finally, in Sections 2 and 3 we also characterized strict 2-categories, pseudo double categories, and strict double categories by imposing associativity and unit laws. These axioms can be added to the monad presentations, so we have:

**Proposition 5.8.** *The category 2-Cat of 2-categories (and strict functors) is monadic over the category 2-Cptd of 2-computads.*

*Likewise, the categories $\mathbf{DblCat}$ and $\mathbf{PsDblCat}_{\mathrm{st}}$ of strict double categories and pseudo double categories (both with strict functors) are monadic over the category $\mathbf{DblCptd}$ of double computads.* $\square$

The situation is summarized by chains of forgetful functors

$$2\text{-}\mathbf{Cat} \rightarrow \mathbf{W}\text{-}2\text{-}\mathbf{Cat}_{\mathrm{st}} \rightarrow \mathbf{I}\text{-}2\text{-}\mathbf{Cat} \rightarrow 2\text{-}\mathbf{Cptd}$$

and

$$\mathbf{DblCat} \rightarrow \mathbf{PsDblCat}_{\mathrm{st}} \rightarrow \mathbf{WDblCat}_{\mathrm{st}} \rightarrow \mathbf{IDblCat} \rightarrow \mathbf{DblCptd}$$

all compositions of which are monadic, using Lemma 4.3.

*Remark 5.9.* The left adjoint $\mathbf{I}\text{-}2\text{-}\mathbf{Cat} \rightarrow 2\text{-}\mathbf{Cat}$ is in fact the obvious subcategory inclusion, sending implicit 2-categories to their path 2-categories. The left adjoint $\mathbf{IDblCat} \rightarrow \mathbf{DblCat}$ is similar.

The composite $\mathbf{W}\text{-}2\text{-}\mathbf{Cat}_{\mathrm{st}} \rightarrow \mathbf{I}\text{-}2\text{-}\mathbf{Cat} \rightarrow 2\text{-}\mathbf{Cat}$ (forget then free) is the usual strictification functor for bicategories, which we described explicitly in Proposition 2.5. Analogously, the composite $\mathbf{WDblCat}_{\mathrm{st}} \rightarrow \mathbf{IDblCat} \rightarrow \mathbf{DblCat}$ provides a strictification functor for doubly weak double categories; in the next section we will show that every doubly weak double category is equivalent to its strictification in a suitable sense.

## 6. ICONS AND 2-MONADS

In this section we will see that $\mathbf{I}\text{-}2\text{-}\mathbf{Cat}$ and $\mathbf{IDblCat}$ can be enhanced to 2-categories. (One furthermore expects the instances of a two-dimensional categorical structure to be objects in a *three*-dimensional categorical structure; transformations and modifications of implicit 2-categories are discussed in Appendix A.)

As is standard in the theory of bicategories, we cannot directly define a (weak or strict) 2-category of bicategories, pseudofunctors, and transformations: vertical