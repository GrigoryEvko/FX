We will abuse language and say that a simplicial groupoid “is a category” when it is in the essential image of $N^{gpd}$ and will identify this simplicial groupoid with the corresponding category.

**Theorem 5.5** *There exists a localic groupoid $\mathbb{G}_{KH}$ such that, naturally in locales $X$,*

$$\mathbf{KHaus}_X^{op} \simeq Prin_{\mathbb{G}_{KH}}^{\Delta}(X).$$

*In particular, $Prin_{\mathbb{G}_{KH}}^{\Delta}(X)$ is a category for all locales $X$.*

To be clear, what we mean here is that $N^{gpd}(\mathbf{KHaus}_X^{op}) \simeq Prin_{\mathbb{G}_{KH}}^{\Delta}(X)$.

*Proof:* In [HT22] it is shown that for any category $\mathcal{C}$, $[\mathcal{C}, \mathbf{KHaus}] \simeq \mathbf{KHaus}_{\mathcal{C}}$ where $\mathcal{C}$ is the topos of presheaves on $\mathcal{C}$. The account in [HT22] is constructive and natural in $\mathcal{C}$. So it can be carried out relative to $Sh(X)$ for any locale $X$; applying it to the case $\mathcal{C} = \{0 \leq 1 \leq \cdots \leq n\}$ we have an equivalence of categories

$$[\{0 \leq 1 \leq \cdots \leq n\}^{op}, \mathbf{KHaus}_X] \simeq \mathbf{KHaus}_{\mathbb{S}_n \times X} \simeq Prin_{\mathbb{G}_{KH}}^{\Delta}(X)([n]),$$

In particular, restricting to invertible arrows on both sides, we obtain exactly that $Prin_{\mathbb{G}_{KH}}^{\Delta}(X)$ identifies with the groupoid nerve of the opposite category of $\mathbf{KHaus}_X$. $\square$

To show that this Theorem is the compact Hausdorff dual of the well known fact that there is a classifying localic groupoid for the geometric theory of objects, we re-state this well know result in the following form:

**Theorem 5.6** *There exists a localic groupoid $\mathbb{G}_{Dis}$ such that, naturally in locales $X$,*

$$\mathbf{Dis}_X \simeq Prin_{\mathbb{G}_{Dis}}^{\Delta}(X).$$

*Proof:* To find $\mathbb{G}_{Dis}$ the easiest reference is Corollary 5.2 of [B90] from which we can establish $\mathbf{Dis}_X^{\cong} \simeq Prin_{\mathbb{G}_{Dis}}(X)$ by considering the case of the object classifier. We can also reach this conclusion by exploiting the same reasoning as used above to find $\mathbb{G}_{KH}$; rather than $NDL$, use the geometric theory consisting of a single object. Discrete locales are locally compact and so are exponentiable allowing the last step of the proof of Proposition 4.4 to work. As for the correspondence between morphisms in $\mathbf{Dis}$ and $\mathbb{S}$-homotopies, this is clear from Lemma B4.2.3 of [J02] given that $Sh(\mathbb{S} \times X) \simeq [\{0 \leq 1\}, Sh(X)]$ (take $\mathbb{T}$ to be the object theory $\mathbb{O}$), and this easily generalizes to $Sh(\mathbb{S}_n \times X) \simeq [\{0 \leq 1 \leq \cdots \leq n\}, Sh(X)]$ showing that we have an equivalence of categories

$$Prin_{\mathbb{G}_{Dis}}^{\Delta}(X)([n]) \simeq [\{0 \leq 1 \leq \cdots \leq n\}, \mathbf{Dis}_X].$$

After restricting to invertible morphisms on both sides we see that $Prin_{\mathbb{G}_{Dis}}^{\Delta}(X)$ is the nerve of $\mathbf{Dis}_X$. $\square$

10