9 Relation to algebraic patterns

51

# 1 Introduction

At the present time, monads on $\infty$-categories are arguably difficult to work with. In [16], Jacob Lurie developed a relatively nice theory of monads on $\infty$-categories as a byproduct of his theory of $\infty$-operads and proved the Barr-Beck monadicity theorem for $\infty$-categories. Essentially, a monad is defined there as a monoid object in the monoidal $\infty$-category of endofunctors. However, this theory remains relatively difficult to use in practice due to the fact that unpacking all the definitions involved in the previous sentence takes a lot work (we review this in Section 3). Also many classical theorems about monads have not yet been proven in this context. For example, it does not seem possible to deduce from [16]$^1$ that the category of algebras for an accessible monad on a cocomplete category has all colimits.

Riehl and Verity proposed an alternative, simpler, definition of monads in [18] for which they also proved the Barr-Beck monadicity criterion. But it is also more model dependent than Lurie's definition as it relies on a strict action of a simplicial monoid on a quasi-category.

This paper is meant to be a toolbox filling some of these gaps and offering a new way to work with (most) monads on $\infty$-categories using only basic $\infty$-category theory instead of Lurie's theory of operads and in an essentially model independent way. This is mostly based on an $\infty$-categorical adaptation of the work on Bourke and Garner in [4] for 1-categorical monads.

Versions of the monad-theory adjunction have appeared in the category theory literature since the 1960s, beginning with Linton's result ([14]). In [4], Bourke and Garner developed a very general monad-theory adjunction, which encompassed many, if not all, of the previously known constructions. Disregarding the enriched category theoretic aspect for simplicity, if $\mathcal{A} \subset \mathcal{E}$ is a small dense full subcategory, an $\mathcal{A}$-pretheory is just a bijective on objects (or essentially surjective) functors $\mathcal{A} \to \mathcal{K}$, with $\mathcal{K}$ a small $\infty$-category. Any monad $M$ on $\mathcal{E}$ has an attached pretheory, called its theory, which is the full subcategory of the Kleisli category of $M$ of objects that are in $\mathcal{A}$.

$^1$Lurie's work contains some results about colimits in category of algebras, but as far as we know, in the case of monads they only applies when the monad preserves colimits and hence colimits of algebras are just colimits in the underlying category.

2