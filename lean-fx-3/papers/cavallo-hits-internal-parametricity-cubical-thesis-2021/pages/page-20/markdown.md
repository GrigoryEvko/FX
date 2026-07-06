8 Introduction

|  Judgment | Reading  |
| --- | --- |
|  $A$ type | $A$ is a type  |
|  $A = A'$ type | $A$ and $A'$ are equal types  |
|  $M \in A$ | $M$ is an element of type $A$  |
|  $M = M' \in A$ | $M$ and $M'$ are equal elements of type $A$  |

Figure 1.1: Judgments of a type theory (simplified)

of the typing judgment $M \in A$. For a trivial example, a program $F \in \text{Int} \rightarrow \text{Int}$ validates the (boring) theorem “for every integer, there exists an integer”. To express something more involved, like the existence of additive inverses, we need more sophisticated types; with the machinery we will develop in Chapter 2, the type of additive inverse functions can be written as follows.

$$(n : \text{Int}) \rightarrow (m : \text{Int}) \times \text{Id}(\text{Int}, m + n, 0)$$

Glossed, this is the type of functions that take an input integer $n \in \text{Int}$ and output a pair of results: another integer $m \in \text{Int}$, but also a certificate that $m + n$ is equal to 0. This “type of certificates” $\text{Id}(\text{Int}, m + n, 0)$ is called an identity type: its elements are proofs that $m + n$ and 0 are identical (or identified) as elements of Int. To set up a type theory including such types, we must answer a tricky question: what kind of program constitutes a proof that two integers are the same? More broadly, how do we understand proofs of equality from a computational perspective? These questions are at the root of this thesis; as we will see, they are not at all straightforward to answer.

The history of identity types is a complex one, entangled intimately with a distinction between “extensional” and “intensional” type theories. But until relatively recently, all computational explanations of identity types have shared a common feature: the programs classified by an identity type $\text{Id}(A, M, N)$ are computationally trivial. That is, the output or computational behavior of a program $P \in \text{Id}(A, M, N)$ (“$M$ and $N$ are identified in $A$”) is uninteresting; the only interesting question is whether such a program exists. This seems natural from a classical mathematical perspective: once you have proven two objects are equal, you need never again to think about why or how they are equal. You merely cite the theorem when you need it. However, committing to this apparently innocuous conception of equality in a computational setting actually has disastrous consequences for mathematical reasoning. For the purposes of this thesis, the most notable casualty is the quotient type.

**Effective quotients** Given a type $A$, a quotient of $A$ is, roughly speaking, a type that has the same elements of $A$ but where some previously distinct elements are now regarded as equal. As a simple example, we might define the integers modulo $n$ ($\text{Int}_n$) for any natural