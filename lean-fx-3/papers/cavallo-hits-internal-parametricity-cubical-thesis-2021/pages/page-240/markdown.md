228

Introduction

has an underlying pointwise element derivable through the use of the modal operators, mirroring the interpretation of the formalism into the set-theoretic model. What we can say, then, is that pointwise terms that arise from parametric terms satisfy parametricity properties.

Getting a bit more specific, we draw our modal operators from the theory of axiomatic cohesion, defined by Lawvere [Law07] in a categorical setting and first formulated in type-theoretic terms by Schreiber and Shulman [SS12; Shu18]. To say that a category C is cohesive over another category D is, on an intuitive level, to say that objects of C are “spaces” whose collections of “underlying points” are objects of D. (A category is a collection of objects equipped with a notion of function between objects satisfying certain axioms.)

As a representative example, let us consider the category of cartesian cubical sets PSh(Dc), which we have used to model a cubical formalism in Section 3.3.1. Recalling briefly the definition from that section, an object of PSh(Dc) is a family of sets indexed by contexts of interval variables, with functions between them for each interval substitution.

Definition (Replica of Definition 3.3.2). A cubical set G consists of the following data.

- For every context $\Psi = (x_1 : \mathbb{I}, \ldots, x_n : \mathbb{I})$, a set $G(\Psi)$.
- For every substitution $\psi = (r_1/x_1, \ldots, r_n/x_n)$ replacing the variables of a context $\Psi$ as above with terms in a context $\Psi'$ (variables or 0,1), a function $G(\psi) : G(\Psi) \to G(\Psi')$.

We ask that G preserve identity and composition of substitutions.

The intuition is that a cubical set G is a “space” described as an assemblage of higher-dimensional cubes. Each set $G(x_1 : \mathbb{I}, \ldots, x_n : \mathbb{I})$ is the collection of n-dimensional cubes of the space: $G(\cdot)$ is the set of points, $G(x : \mathbb{I})$ is the set of lines, $G(x : \mathbb{I}, y : \mathbb{I})$ is the set of squares, and so on. The substitution functions, meanwhile, explain how the cubes attach to each other. Given a line $g \in G(x : \mathbb{I})$, for example, we have a pair of points $G(0/x)(g), G(1/x)(g) \in G(\cdot)$ representing the endpoints of that line.

The category of cubical sets is cohesive over the category of sets, Set: a cubical set G consists of a set $G(\cdot)$ of underlying points equipped with spatial information in the form of higher-dimensional path structure. In Lawvere’s formulation, this is captured by a chain of four functors (functions between categories) relating the two and satisfying