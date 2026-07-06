Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:43

vertices of $H$ and $K$ (with direction depending on the sign of that vertex). Similarly, we obtain a map in the other direction, and the two are inverses.

When $\iota$ is an inclusion $\partial(\mathcal{C}_{/\Psi}) \hookrightarrow \mathcal{C}_{/\Psi}$, we must show that given two expansions $H, K : \mathcal{C}_{/\Psi} \to \mathcal{P}$ of $\pi$-extremal lifts, any isomorphism $\alpha : H' \cong K'$ between their corresponding pre-expansions $H', K' : \partial(\mathcal{C}_{/\Psi}) \to \mathcal{P}$ is also an isomorphism $H \cong K$. Since the inclusion $\partial(\mathcal{C}_{/\Psi}) \hookrightarrow \mathcal{C}_{/\Psi}$ is bijective on objects, this is just an extra naturality condition with respect to the factorization morphism. But the two sides of this desired naturality square each fit into an expansion of $H$ whose expanders are those of $K$ composed with components of $\alpha$ or their inverses; hence they are equal.

Finally, when $\iota$ is a codiagonal $\mathcal{C}_{/\Psi} +_{\partial(\mathcal{C}_{/\Psi})} \mathcal{C}_{/\Psi} \to \mathcal{C}_{/\Psi}$ or an inclusion $\mathcal{C}'_{\cong} \hookrightarrow \mathcal{C}_{\cong}$, full-faithfulness is automatic since these $\iota$'s are bijective on objects and full. $\square$

**Proposition 7.5.** *For any sorted doctrine $\mathbb{D}$ and any well-sorted $\mathbb{D}$-sketch $\mathcal{S}$, the completion $\widehat{\mathcal{S}}_{\mathbb{D}}$ is also well-sorted.*

*Proof.* Let $\mathcal{S}$ be well-sorted, and let $(\widehat{\mathcal{S}}_{\mathbb{D}})' \to \widehat{\mathcal{S}}_{\mathbb{D}}$ be the well-sorted coreflection of $\widehat{\mathcal{S}}_{\mathbb{D}}$. Since $\mathcal{S}$ is well-sorted, the map $\mathcal{S} \to \widehat{\mathcal{S}}_{\mathbb{D}}$ factors through $(\widehat{\mathcal{S}}_{\mathbb{D}})'$. But by Proposition 6.11, $(\widehat{\mathcal{S}}_{\mathbb{D}})'$ is $\mathbb{D}$-complete, so the universal property of $\widehat{\mathcal{S}}_{\mathbb{D}}$ induces a map $\widehat{\mathcal{S}}_{\mathbb{D}} \to (\widehat{\mathcal{S}}_{\mathbb{D}})'$ that is a section of the coreflection, up to isomorphism. This implies that $\widehat{\mathcal{S}}_{\mathbb{D}}$ is also well-sorted. $\square$

## 8. THE SEQUENT CALCULUS OF A DOCTRINE

Let $\mathbb{D}$ be an LNL doctrine and $\mathcal{S}$ an LNL polycategory with a map $\pi : \mathcal{S} \to |\mathbb{D}|$, which we regard as a $\mathbb{D}$-sketch with no proto-extremal cones. Then Theorem 7.4 implies that $\mathcal{S}$ generates a free $\mathbb{D}$-category $\widehat{\mathcal{S}}_{\mathbb{D}}$. We now extract a sequent calculus that presents such free $\mathbb{D}$-categories from the proof of Theorem 7.4.

For simplicity, for now we suppose that $\mathbb{D}$ is unsorted, $|\mathbb{D}|$ is subterminal, and all the cones of $\mathbb{D}$ are *discrete* (have no nonidentity abstract transitions) and also *finite*. This restriction on cones includes cones for universal morphisms, as in Definition 4.16, and also for finite products and coproducts, as in Definition 4.18. These are the primary universal properties that are traditionally considered in logic. Under these assumptions, we can replace the construction of Corollary 7.3 by the following simplified version.

- (i) First perform the small object argument starting at $\mathcal{S}_0 = \mathcal{S}$, using only the inclusions $\partial\mathcal{C} \hookrightarrow \mathcal{C}$ for $\mathbb{D}$-cones $\mathcal{C}$, and when $n > 0$ restricting the coproduct to include only the morphisms $u : \partial\mathcal{C} \to \mathcal{S}_n$ that do not factor through $\mathcal{S}_{n-1}$. After a countable iteration, this produces a precomplete sketch $\mathcal{S}_\omega$.
- (ii) Next perform the small object argument starting at $\mathcal{S}_\omega$, using only the inclusions $\partial(\mathcal{C}_{/\Psi}) \hookrightarrow \mathcal{C}_{/\Psi}$ and their codiagonals $\mathcal{C}_{/\Psi} +_{\partial(\mathcal{C}_{/\Psi})} \mathcal{C}_{/\Psi} \to \mathcal{C}_{/\Psi}$. After a further countable iteration, this produces a realized sketch $\mathcal{S}_{\omega+\omega}$. Moreover, since these inclusions and codiagonals are bijective on objects and each $\partial\mathcal{C}$ is discrete, $\mathcal{S}_{\omega+\omega}$ is still precomplete.
- (iii) Finally, perform one step of the small object argument using the map $\mathcal{C}'_{\cong} \hookrightarrow \mathcal{C}_{\cong}$. This is sufficient to produce a saturated sketch $\widehat{\mathcal{S}}_{\mathbb{D}} = \mathcal{S}_{\omega+\omega+1}$, which is still precomplete and realized, and hence $\mathbb{D}$-complete.

In particular, these changes make the argument completely constructive. (The negation in (i) may not seem constructive, but the inclusion of $\mathcal{S}_{n-1}$ into $\mathcal{S}_n$ is decidable on objects because each $\partial\mathcal{C} \hookrightarrow \mathcal{C}$ is.)