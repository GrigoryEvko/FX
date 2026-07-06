two constructions induce an equivalence between the category of weakly spatial Banach locales (and linear map) and the category of Banach spaces (with bounded linear map).

## 4.2 The Localic Gelfand duality

4.2.1. **Definition :** A $C^*$ locale (or localic $C^*$ algebra) is a Banach locale $\mathcal{C}$, endowed with an involution $* : \mathcal{C} \to \mathcal{C}$ and a product $\mathcal{C} \times \mathcal{C} \to \mathcal{C}$ which satisfy the usual axioms for a $C^*$ algebra:

- $\mathcal{C}$ is a $\mathbb{C}$ algebra (i.e. the product is associative, distributes over the addition and is compatible with the action of $\mathbb{C}$).
- The $*$ involution is $\mathbb{C}$ anti-linear and satisfies $(ab)^* = b^*a^*$.
- One has: $\|ab\| \leqslant \|a\|\|b\|$.
- One has: $\|a^*a\| = \|a\|^2$.

All the axioms are equalities (or inequalities with respect to the specialization order), hence are clearly preserved by pull-back and therefore if $\mathcal{C}$ is a $C^*$ algebra and $f$ is a geometric morphism to the base topos then $f^\#(\mathcal{C})$ is also a $C^*$ locale. And if $\mathcal{C}$ is a (pre)-Banach locale endowed with an $*$ map and a map $\mathcal{C} \times \mathcal{C} \to \mathcal{C}$ such that for some open surjection $f$, $f^\#(\mathcal{C})$ is a $C^*$ algebra for those structure then $\mathcal{C}$ is a $C^*$ algebra.

The main result of this section will be an anti-equivalence of categories between the categories of abelian unital $C^*$ locales and compact regular locales. The “difficult” part lies in the construction of the two functors, and the proof that they are compatible with pull-back along geometric morphisms. Indeed once it is done, one can apply 2.3.17 to reduce the proof of the equivalence to the case of spatial $C^*$ algebras and completely regular compact locales which is already known ([1] [7]). Actually, even the construction of the two functors could be avoided since we know that the notion of $C^*$ locale is the “stackification” of the notion of $C^*$ algebra (it is a direct consequence of the observations made in 3.6.5), and one can prove (applying 2.6.6) a similar result for compact regular locales and compact completely regular locales. Hence the already known equivalence between unital abelian $C^*$ algebras and compact completely regular locales immediately yields the equivalence between the “stackified” notions, but we think that it is important to have an explicit construction of these functors without having to use descent theory.

4.2.2. **Proposition :** Let $X$ be a compact regular locale, then $[X, \mathbb{C}]$ is a $C^*$ algebra, for the addition, product and involution given by the addition, the product and the complex conjugation of $\mathbb{C}$, and the norm given by:

$$B_q 0 = [X \ll f^* D_q]$$

54