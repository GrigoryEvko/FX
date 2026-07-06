conclude that the free braided monoidal groupoid monad is extended by the free $E_2$-space monad.

*Remark 8.16.* If $n \geq 3$, is not possible to find a monad on Gpd whose algebraic theory has as its $\mathcal{S}$-models $E_n$-spaces. The reason is that by [16, Corollary 5.1.1.7], $E_\infty$-algebras and $E_n$ algebras in Gpd coincide for $n \geq 3$, so the existence of a theory with the required properties would imply that $E_\infty$-spaces are the same as $E_n$-spaces. The aforementioned fact can be viewed as an analogue of the Baez-Dolan stabilization hypothesis (see [1] and [16, Example 5.1.2.3]).

It should be noted that for all $2 < n < \infty$, the free $E_n$-algebra on a set $X$ has homotopy groups in arbitrary large dimension, i.e. is not $k$-truncated for any $k$. So replacing $\mathcal{B}$ by the category of $k$-groupoids for a larger $k$ does not allow one to deal with the case of $E_n$-algebra for larger $n$ even if the argument above does not obstruct it.

## 9 Relation to algebraic patterns

Finally, we clarify the relation between our results and Chu and Haugseng's theory of algebraic patterns from [5]. In a very simplified way, algebraic patterns are a type of 'theory' that through the monad-theory adjunction corresponds to cartesian parametric right adjoint$^5$ monads on presheaf categories.

A natural transformation is said to be *cartesian* if all of its naturality squares are cartesian. A monad is said to be cartesian if its unit and composition natural transformation $Id \rightarrow M$ and $M \rightarrow M^2$ are cartesian. This also implies that all other structural morphisms of the monad are cartesian. A parametric right adjoint monad is a monad whose underlying functor $M : \mathcal{C} \rightarrow \mathcal{C}$ admits a right adjoint when considered as a functor $\mathcal{C} \rightarrow \mathcal{C}/M(1)$ for 1 a terminal object of $\mathcal{C}$.

Note that [5] defines models in terms of covariant functors to Set while we use presheaves, i.e. contravariant functors as in the 1-categorical tradition (like [2] or [4]). To simplify the connection between the present paper and [5], we will rephrase the definitions given in [5] in terms of the opposite categories.

$^5$which are called polynomial monads in [5].

51