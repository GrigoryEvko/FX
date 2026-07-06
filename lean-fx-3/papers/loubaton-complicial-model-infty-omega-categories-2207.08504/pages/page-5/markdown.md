# Introduction

A *category* consists of a set of objects, and for any pair of objects $a, b$, a set of morphisms $\hom_C(a, b)$ equipped with composition operations satisfying associativity laws.

$(\infty, 1)$-*Categories* are a homotopical generalization of categories. Intuitively, they are defined similarly to categories, except that we replace sets of objects and morphisms with spaces of objects and morphisms, and the associativity and unit laws are no longer satisfied strictly but homotopically.

Thanks in particular to the work of Joyal ([Joy02]) and Lurie ([Lur09]), most of the important concepts and theorems of category theory now have their $(\infty, 1)$-categorical analogues. These objects have become important tools in many areas of mathematics, including algebraic geometry, algebraic topology, and representation theory.

Another generalization of the notion of category is obtained by replacing the set of morphisms between two objects $a$ and $b$ with a category of morphisms between $a$ and $b$. These new objects are called *2-categories*. By replacing sets of morphisms between two objects $a$ and $b$ with $(n-1)$-categories of morphisms between $a$ and $b$, one can define by induction the notion of $n$-*category* for any integer $n$, and by limit, the notion of $(\infty, \omega)$-category.

For $n \in \mathbb{N} \cup \{\omega\}$, the notion of $(\infty, n)$-category is obtained by making both of these generalizations simultaneously. These objects are now found in many areas, including derived algebraic geometry, where the 6-functors formalism is expressed and manipulated using the theory of $(\infty, 2)$-categories ([GR19]), and in topological quantum field theory, where $(\infty, n)$-categories are essential for formulating and proving the cobordism hypothesis ([BD95], [Lur08], [GP21], [CS19]).

This text is devoted to the study of *models of $(\infty, n)$-categories*. By this, we mean any model category whose associated $(\infty, 1)$-category is $(\infty, n)$-cat. Among the known models of $(\infty, n)$-categories, we have for example Rezk's complete Segal $\Theta_n$-spaces, $n$-fold Segal spaces, and Segal $n$-categories (we refer to [BSP21] for a comprehensive presentation of these models and their equivalence). The common feature of all the models we have mentioned is that they rely on a globular combinatoric.

The main result of this text is to demonstrate that *complicial sets*, defined and extensively studied by Verity, are a model for $(\infty, n)$-categories. Unlike the other models, complicial sets rely on the combinatorics of the iterated lax cone, i.e. the combinatorics of simplices.

Let's now try to explain the intuition underlying the definition of complicial sets. To do this, we must first introduce stratified simplicial sets. A *stratified simplicial set* is a pair $(K, tK)$ where $K$ is a simplicial set and $tK$ is a subset of the simplices of $K$ containing the degenerate simplices. A simplex in $tK$ is called *marked*. We denote by $\text{tPsh}(\Delta)$ the category of stratified simplicial sets.

5