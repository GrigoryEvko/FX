2. The terminal object is $\Gamma$.
3. Given ordinals $\mu \leq \lambda < \kappa$ and objects $A_\lambda, A_\mu \in \mathcal{C}(\Gamma)$, the display maps between them are the maps in $Hom_{\mathcal{C}(\Gamma)}(A_\lambda, A_\mu)$ which are also fibrations of $\mathcal{C}$. We group these maps and objects in $Dis(\mathcal{C}(\Gamma))$, which is easily seen to be a subcategory.
4. $Dis(\mathcal{C}(\Gamma))$ is closed under transfinite compositions, since $\mathcal{C}$ is itself closed under such compositions.
5. The inclusion functor $i: Dis(\mathcal{C}(\Gamma)) \hookrightarrow \mathcal{C}(\Gamma)$ preserve transfinite compositions.
6. If $A \twoheadrightarrow B$ is an arrow in $Dis(\mathcal{C}(\Gamma))$, then $B \in Ob_\mu(\mathcal{C}(\Gamma))$ and $A \in Ob_\lambda(\mathcal{C}(\Gamma))$ for some ordinals $\lambda, \mu$ with $\mu \leq \lambda$: This follows directly by the definition of the objects of $\mathcal{C}(\Gamma)$
7. For any object $A \in Ob_\lambda(\mathcal{C}(\Gamma))$ and any $\mu \leq \lambda$, there exists a unique object $B \in Ob_\mu(\mathcal{C}(\Gamma))$ and a unique display map $A \twoheadrightarrow B$: We can easily obtain this by induction on $\lambda$ and verify that the map has the correct length.
8. Canonical pullbacks: This is given by the category with attributes structure on $\mathcal{C}$, as explained in theorem B.58.
9. Canonical pullbacks are strictly functorial: This is exactly what theorem B.58 achieves.
10. It follows from the description of objects given above.

Before we can state our main result, we first need to state the appropriate notion of equivalence between $\kappa$-clans. We borrow the definitions from [Joy17] adapted to our setting. Let $\mathcal{C}$ and $\mathcal{E}$ be two $\kappa$-coclans. We say that a functor $F: \mathcal{C} \to \mathcal{E}$ is a *morphism of $\kappa$-coclans* if

1. sends initial objects to initial objects,
2. preserves cofibrations,
3. preserves pushouts of cofibrations along any map
4. preserves transfinite compositions.

142