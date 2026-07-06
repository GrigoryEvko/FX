1:24

M. SHULMAN

Vol. 19:2

of Proposition 2.16 (universal morphisms compose) would have on the order of 25 different cases to consider.⁴ Similarly, there are four different kinds of limits and colimits, and so on. Duality doesn't simplify the situation significantly either, since an LNL polycategory has no "opposite" that reverses the nonlinear morphisms. Nevertheless, there is a clear intuition that this technical multiplicity is in some sense "inessential": all the cases behave similarly. In this section we give an alternative definition of LNL polycategories that enables us to formally unify these cases.

Given a set of objects partitioned into linear and nonlinear ones, by a **signed object** we mean an object together with an element of $\{-, +\}$, written $R^+$ or $R^-$, where $R$ is a (linear or nonlinear) object. We denote general signed objects by letters towards the middle of the Roman alphabet such as $K, L, M, \dots$, and lists of signed objects by the Greek letters $\Phi, \Psi$. If $K$ is a signed object we write $K^\bullet$ for the result of flipping its sign: $(R^+)^\bullet = R^-$ and $(R^-)^\bullet = R^+$.

**Definition 4.1.** A list of signed objects is **admissible** if

- (i) it contains at most one positive nonlinear object, and
- (ii) if it does contain one such, then it contains no linear objects.

**Lemma 4.2.** *If $(\Phi, K)$ and $(K^\bullet, \Psi)$ are admissible, so is $(\Phi, \Psi)$.*

*Proof.* If a positive nonlinear object $X^+$ appears in $\Phi$, then $K$ and all other objects in $\Phi$ must be negative nonlinear. Hence $K^\bullet$ is positive nonlinear, so all objects in $\Psi$ are also negative nonlinear. We can argue similarly if $\Psi$ contains $X^+$. $\square$

By a **structural map** we mean a morphism $\sigma : (K_1, \dots, K_m) \to (K_{\sigma 1}, \dots, K_{\sigma n})$ where $(K_1, \dots, K_m)$ is a list of signed objects and $\sigma : \{1, \dots, n\} \to \{1, \dots, m\}$ is a function with the property that for any $j$ with $1 \le j \le m$, if $|\sigma^{-1}(j)| \ne 1$ then $K_j$ is negative and nonlinear.

**Definition 4.3.** An **entries-only LNL polycategory** $\mathcal{P}$ consists of:

- A set of **objects** partitioned into linear and nonlinear ones.
- For any admissible list of signed objects $(K_1, \dots, K_n)$, a hom-set $\mathcal{P}(K_1, \dots, K_n)$, with functorial actions $\mathcal{P}(\Psi) \to \mathcal{P}(\Phi)$ by structural maps $\sigma : \Phi \to \Psi$.
- For any object $R$ (linear or nonlinear), an identity $1_R \in \mathcal{P}(R^-, R^+)$.
- Whenever $(\Phi, K)$ and $(K^\bullet, \Psi)$ are admissible, a composition map

$$\circ_K : \mathcal{P}(K^\bullet, \Psi) \times \mathcal{P}(\Phi, K) \to \mathcal{P}(\Phi, \Psi)$$

that is associative, unital, and equivariant with respect to the structural actions and permutations that swap the two inputs.

A **functor** between entries-only LNL polycategories consists of functions between their linear and nonlinear objects and morphisms, preserving entries, structural actions, identities, and composites.

**Proposition 4.4.** *The category of entries-only LNL polycategory is equivalent to that of LNL polycategories.*

⁴Not exactly 25, of course, since some pairs of universal morphisms will not be composable.