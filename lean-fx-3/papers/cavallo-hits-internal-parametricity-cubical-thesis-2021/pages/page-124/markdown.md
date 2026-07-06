112 General higher inductive types

|  Judgment | Reading  |
| --- | --- |
|  $$\Gamma \gg \Delta \text{ tel}$$ | $$\Delta$$ is a telescope of types  |
|  $$\Gamma \gg \delta \in \Delta$$ | $$\delta$$ is an instantiation of $$\Delta$$  |
|  $$\Gamma \gg \Delta \blacktriangleright \mathcal{K} \text{ spec}$$ | $$\mathcal{K}$$ specifies a $$\Delta$$-indexed HIT  |
|  $$\Gamma \gg \Delta \blacktriangleright \mathcal{K} \rightarrow \mathcal{K}'$$ | $$\mathcal{K}'$$ is a prefix of $$\mathcal{K}$$  |
|  $$\Gamma \gg \Delta \mid \mathcal{K} \blacktriangleright \mathcal{C} \text{ constr}$$ | $$\mathcal{C}$$ is a constructor definition over $$\mathcal{K}$$  |
|  $$\Gamma \gg \Delta \blacktriangleright \mathcal{K} @ \ell \Rightarrow (\mathcal{K}' \mid \mathcal{C})$$ | $$\mathcal{C}$$ appears in $$\mathcal{K}$$ with label $$\ell$$, preceded by $$\mathcal{K}'$$  |
|  $$\Gamma \gg \Delta \mid \mathcal{K} \blacktriangleright \Theta \text{ actx}$$ | $$\Theta$$ is a context of recursive argument types over $$\mathcal{K}$$  |
|  $$\Gamma \gg \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright \text{A atype}$$ | $$\text{A}$$ is a recursive argument type over $$\mathcal{K}$$ and $$\Theta$$  |
|  $$\Gamma \gg \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright \text{M} \in \text{A}$$ | $$\text{M}$$ is an argument term of type $$\text{A}$$  |
|  $$\Gamma \gg \Delta \mid \mathcal{K} \mid \Theta' \blacktriangleright \theta \in \Theta$$ | $$\theta$$ is an argument substitution from $$\Theta'$$ to $$\Theta$$  |

Figure 6.1: Judgments used in the definition of HIT specifications

tor given such data, and showing that said eliminator is indeed well-typed and validates the expected reduction rules. Like coercion, the final step requires an argument by the universal property of the inductive type relation as a least fixed-point.

Finally, in Section 6.5, we describe the *validity restriction*, an adjustment to the homogeneous composition operation introduced by Angiuli, Favonia, and Harper [AFH18] that enables a stronger characterization of the values of a higher inductive type.

## 6.1 Specifications

To give a computational interpretation of higher inductive types, we must first settle on a definition of higher inductive type. We define a class of HIT specifications relative to a value type system by way of a judgment $$\Gamma \gg \Delta \blacktriangleright \mathcal{K}$$ spec, read “$$\mathcal{K}$$ is a higher inductive type specification indexed by $$\Delta$$ in context (*i.e.*, with parameters) $$\Gamma$$”. To define this judgment, we make use of a series of auxiliary judgments, catalogued in Figure 6.1, that define the well-formed constructors, recursive argument types, and boundary terms. (Each of the judgments in this figure is the unary form of a binary judgment.) These judgments are all defined relative to an ambient value type system, which we leave implicit in this section. The raw grammar of specifications, constructors, and so on is shown in Figure 6.2; the judgments operate on syntax drawn from said grammar.

The final four judgments of Figure 6.1—contexts, types, terms, and substitutions—constitute a small formal type theory within which the recursive parts of a specification are defined. For lack of a better name, we refer to these as *argument* contexts, types, terms, and substitutions respectively. Argument types are used to specify the types of recursive arguments to constructors, while argument terms appear in two places: as in-