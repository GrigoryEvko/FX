12 Introduction

We can formulate paths in terms of functions out of an *interval space* “$\mathbb{I}$”, a space consisting of two points with a single path between them.

A path from **A** to **B** in our example space $X$ is the same as a continuous function $\mathbb{I} \rightarrow X$ that sends **0** to **A** and **1** to **B**; in other words, a path is a picture of $\mathbb{I}$ drawn in $X$. A homotopy, being a path between paths, is then a function $\mathbb{I} \rightarrow (\mathbb{I} \rightarrow X)$, or equivalently a function $\mathbb{I} \times \mathbb{I} \rightarrow X$ from the product of two intervals into $X$.

This will be the central organizing concept of the type theory with contentful equality we are about to describe: the representation of equalities in a type as functions from an “interval” into that type.

## 1.2 Realizing contentful equality

We now apply the two preceding ideas, equality as path and as effecting transport, to the design of type theory. We arrive at *cubical type theory*, which was first developed in two parallel variations by Cohen, Coquand, Huber and Mörtberg [CCHM15] and Angiuli, Favonia, and Harper [AFH18].

**Interval terms** Cubical type theory enriches Martin-Löf’s type theory with a new *interval object* $\mathbb{I}$, which behaves much like a type and is used to represent equalities. (The interval is not *actually* a type, for technical reasons that we sweep under the rug here.) Following the topological definition, we take *paths* in a type $A$ to be functions from the interval into $A$.

$$P \in \mathbb{I} \rightarrow A$$

Among the elements of the interval are two distinguished “endpoint” constants, $0 \in \mathbb{I}$ and $1 \in \mathbb{I}$. Any path $P \in \mathbb{I} \rightarrow A$ is thus more specifically a path *from P 0 to P 1*. As we are usually interested in paths between a particular pair of elements, we introduce a type of *paths in A with fixed endpoints* $M_0 \in A$ *and* $M_1 \in A$.

$$P \in \text{Path}(A, M_0, M_1)$$

The elements of this type are functions $P \in \mathbb{I} \rightarrow A$ such that $P 0 = M_0 \in A$ and $P 1 = M_1 \in A$. Here we come to one of the subtler aspects of type theory, cubical or otherwise: the “=” here is not the contentful equality we are in the process of fleshing out, but a separate, contentless equality we call *exact equality*. It is necessary to have such a notion of “strict” equality—to formulate the conditions on elements of path types, for one. We merely want to separate it from the paths we use as “mathematical” equalities to avoid the pitfalls of contentless equality. Exact equality differs from path equality on two axes.