Interpreting specifications 119

# Proposition 6.1.9 (Standard admissibilities).

- *Term substitution.* If $\Gamma' \gg \gamma = \gamma' \in \Gamma$ and $\Gamma \gg \Delta \mid \mathcal{K} \blacktriangleright \Theta = \Theta'$ actx, then we have $\Gamma' \gg \Delta\gamma \mid \mathcal{K}\gamma \blacktriangleright \Theta\gamma = \Theta'\gamma'$ actx; the argument substitutions, types, and terms are likewise stable under substitution.
- *Argument substitution.* If $\Gamma \gg \Delta \mid \mathcal{K} \mid \Theta' \blacktriangleright \theta = \theta' \in \Theta$ and $\Gamma \gg \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright A = A'$ atype, then we have $\Gamma \gg \Delta \mid \mathcal{K} \mid \Theta' \blacktriangleright A\theta = A'\theta'$ atype; the argument substitutions and terms are likewise stable under argument substitution.
- *Specification weakening.* If $\Gamma \gg \Delta \blacktriangleright \mathcal{K} \twoheadrightarrow \mathcal{K}'$ and $\Gamma \gg \Delta \mid \mathcal{K}' \blacktriangleright \Theta = \Theta'$ actx, then we have $\Gamma \gg \Delta \mid \mathcal{K} \blacktriangleright \Theta = \Theta'$ actx; the argument substitutions, types, and terms are likewise stable under specification extension.

As with ordinary substitutions, the argument substitutions include identity and weakening substitutions, each of which is the identity on raw terms.

## 6.2 Interpreting specifications

To get from a specification language to a type system closed under HITs, the first step is to define the interpretation of the formal argument type theory. There are two sides of such an interpretation: the syntactic and the semantic (*i.e.*, relational).

On the one hand, an argument type or term may be interpreted as a piece of syntax in the untyped programming language. On the other hand, each argument type may also be interpreted as an operator on indexed value relations, taking an interpretation for the inductive family $\text{IND}(-)$ as input and producing an interpretation of the compound type. For example, given $\Delta \blacktriangleright \mathcal{K}$ spec and a $\Delta$-indexed relation $R$, we would interpret $A \to \text{IND}(\delta)$ at $R$ as relating $\lambda$-values that take terms in $A$ to terms in the instantiation of $R$ at $\delta$. Using the interpretation of argument types as operators on relations, we likewise build up an interpretation of constructors $C$ and then specifications $\mathcal{K}$ as operators on relations. Finally, we define the inductive relation associated to $\mathcal{K}$ to be the least fixed point of its interpretation as a relational operator. With this definition in hand, it becomes straightforward to construct a type system which is closed under (and supports universes closed under) such relations.

### 6.2.1 Syntactic interpretation

We start with the syntactic interpretation of the argument type theory, defined here as a collection of operations taking raw terms of that language to terms in the untyped programming language. We show later on that these raw operations preserve well-typedness in the right circumstances.