# Chapter 1

## Introduction

### 1.1 Equality in type theory

A *(dependent) type theory* is a kind of framework for mathematics organized around the idea of a *type*. “Type theory” is not a term with a precise, universal definition; rather, it is a term with many definitions, some formal and mathematical, others philosophical. In practice, it refers to a vaguely-delimited constellation of systems surrounded by a common literature: a type theory is that which a type theorist studies. Nevertheless, there are some largely-unifying principles that guide the design of type theories. One is, of course, the concept of a type. Another is the idea that type theories are *constructive* or *computational*: that proofs conducted in a type theory have some kind of computational content, or that they are proofs about computational objects. Our own perspective on type theory, which derives from Martin-Löf’s *Constructive Mathematics and Computer Programming* [Mar82] and Constable’s subsequent program of *computational type theory* [Con09], is that type theory is a language for *classifying programs*, that is, reasoning about their computational behavior.

A type, then, is a classifier of programs, which is to say that it is a collection of programs possessing some property. A definition of a type theory consists of a specification of its types and the programs each classifies. For example, a theory might contain a type Int classifying programs that compute integers. Then “$2 + 2$” would be one such program (it computes the integer 4); we say $2 + 2$ is an element of Int (or is a term of type Int, or simply is in Int) and write $2 + 2 \in \text{Int}$. The statements we make in a type theory, dubbed *judgments* by Martin-Löf, assert typehood and elementhood (Figure 1.1).

*Type formers* enable us to build new types from old ones: perhaps $\text{Int} \times \text{Int}$ is the type of programs that compute pairs of integers, while $\text{Int} \rightarrow \text{Int}$ is the type of programs that take an integer as input and output a new integer. In a type theory with a sufficiently expressive collection of type formers, we can formulate complex mathematical results as instances

7