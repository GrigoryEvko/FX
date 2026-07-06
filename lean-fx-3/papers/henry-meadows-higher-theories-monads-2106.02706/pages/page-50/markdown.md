*Proof.* By [16, Example 3.1.3.14], the left adjoint to the forgetful functor is given by $C \mapsto \coprod_{n \geq 0} \operatorname{Sym}^n(C)$, where $\operatorname{Sym}^n$ is as in [16, Construction 3.1.3.9]. Thus, it suffices to show that $\operatorname{Sym}^n(-)$ takes groupoids to groupoids.

Let $\Sigma_n$ be the symmetric group regarded as a category with one object. Unwinding [16, Construction 3.1.3.9], $\operatorname{Sym}^n(C)$ gets identified with the colimit of a diagram $N(\Sigma_n) \rightarrow \mathcal{S}$ which takes the object to $C^n$ and acts by permuting the factors. This can be further identified with the homotopy colimit of a group acting on a space.

Such a homotopy colimit is called a *homotopy orbit space*, and it fits into a homotopy fibre sequence

$$C^n \rightarrow \operatorname{Sym}^n(C) \rightarrow N(\Sigma_n)$$

(for a description of homotopy orbit spaces, and the above fibre sequence, see [7, Chapter 1, Section 6]). The long exact sequence of homotopy groups associated to the above fibre sequence shows that since $N(\Sigma_n), C^n$ are groupoids, so is $\operatorname{Sym}^n(C)$.

**Example 8.14.** By the preceding lemma we can apply 8.9, 8.11 with $\mathcal{O}^\otimes = E^\otimes_\infty, \mathcal{B} = \operatorname{Gpd}$ to show that the monad $\operatorname{Free}^\mathcal{S}_{E_\infty}$ extends $\operatorname{Free}^\operatorname{Gpd}_{E_\infty}$. In other words, the free symmetric monoidal groupoid monad is extended by the Free $E_\infty$-space monad.

Using [16, Example 2.4.2.5] and [16, Proposition 2.4.2.4], we see that the objects of $\operatorname{Alg}_{E^\otimes_\infty}(Gpd)$ can be identified with symmetric monoidal groupoids. By the definition of 1-morphisms in this $\infty$-category can be identified with functors $F: A \rightarrow B$ of symmetric monoidal categories, along with isomorphism $F(-\otimes_A -) \cong F(-) \otimes_B F(-)$, compatible with the commutativity and associativity properties of $A$ and $B$. In other words, they can be identified with monoidal functors. Similarly the 2-morphisms in $\operatorname{Alg}_{E^\otimes_\infty}(Gpd)$ can be identified with monoidal natural transformations. Thus we can identify $\operatorname{Free}^\operatorname{Gpd}_{E_\infty}$ with the classical free symmetric monoidal groupoid monad considered in [3].

**Example 8.15.** The free $E_2$-algebra $\mathcal{S} \rightarrow \operatorname{Alg}_{E^\otimes_2}(\mathcal{S})$ takes an object $X$ to $\coprod_{n \in \mathbb{N}} B^n(X)$, where $B^n(X)$ is the colimit of the braid group action on $X^n$. This functor takes $\operatorname{Gpd}$ to $\operatorname{Alg}_{E^\otimes_2}(\operatorname{Gpd})$, by the same argument as 8.13. As noted in [16, Example 5.1.2.4], the objects of $\operatorname{Alg}_{E^\otimes_2}(\operatorname{Gpd})$ can be identified with braided monoidal groupoids. Thus, as in the preceding example, we can

50