3.6.5. In particular the category of complete metric sets identifies with the full subcategory of the category of complete metric locales composed of weakly spatial locales, and by 2.3.17 any complete metric locale becomes weakly spatial (hence identifies with a complete metric set) after a pull-back to some open locale. We already mentioned that if one defines $\mathcal{C}(\mathcal{T})$ as the category of complete metric locales over $\mathcal{T}$, then, it is a stack for the topology whose covering are open surjections.

From these observations one can deduce that the stack of internal complete metric locales is the stackification (the analogue of sheafication for stack and pre-stack) of the pre-stack of complete metric sets, that is the universal extension of the notion of complete metrics sets for the descent properties along open surjection.

At this point one could obtain the localic Gelfand duality of 4.2.5 directly by observing that the notion of compact regular locale is obtained as the stackification of the notion of compact completely regular locale, and apply the constructive Gelfand duality between compact regular locale and $C^*$ algebra to show that the two pre-stacks are equivalent. This will also avoid the use any of the material of section 3.5, but it will give an extremely uncomfortable definition of the spectrum of a localic $C^*$ algebra. This is why we prefer explicitly constructing the spectrum (in 4.2.3, using the construction of 3.5) before applying the descent argument to show the Gelfand duality.

## 4 Banach locales and $C^*$ locales

### 4.1 Banach locales and completeness

4.1.1. **Definition :** *A pre-Banach locale is a locally positive locale $\mathcal{H}$ endowed with:*

- *A commutative group law: $+ : \mathcal{H} \times \mathcal{H} \rightarrow \mathcal{H}$, with neutral element $0 : * \rightarrow \mathcal{H}$ and an inversion: $x \mapsto -x : \mathcal{H} \rightarrow \mathcal{H}$.*
- *An action of $\mathbb{Q}[i]$ (endowed with the discrete topology), $\mathbb{Q}[i] \times \mathcal{H} \rightarrow \mathcal{H}$, satisfying the usual axioms of a (unital) module.*
- *A norm function $\|\cdot\| : \mathcal{H} \rightarrow \overleftarrow{\mathbb{R}}_+^\infty$*

*where the norm function is expected to satisfy the following conditions:*

- $\forall x, y \in \mathcal{H} \|x + y\| \leqslant \|x\| + \|y\|$
- $\forall \lambda \in \mathbb{Q}[i], \forall x \in \mathcal{H}, \|\lambda x\| = |\lambda|\|x\|$
- $\|0\| = 0$
- $\mathcal{H} = \bigvee_{n \in \mathbb{N}} \{x \|x\| < n\}$

Of course, all the conditions stated in this definition have to be interpreted either in diagrammatic terms or in terms of generalized elements.

50