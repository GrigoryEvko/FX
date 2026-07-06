## Chapter 3

# Complicial sets as a model of  $(\infty, \omega)$ -categories

### Contents

|  **3.1** | **Preliminaries** | **102**  |
| --- | --- | --- |
|  3.1.1 | Segal $A$-precategories | 102  |
|  3.1.2 | Stratified Segal $A$-precategories | 105  |
|  3.1.3 | Models of $(\infty, n)$-categories | 109  |
|  3.1.4 | Gray module | 109  |
|  3.1.5 | Complicial Gray module | 113  |
|  **3.2** | **Complicial Gray module structure on tSeg($A$)** | **114**  |
|  3.2.1 | $\circ$-cone in tSeg($A$) | 114  |
|  3.2.2 | Adjunction with tPsh($\Delta$) | 117  |
|  3.2.3 | Complicial horn inclusions | 118  |
|  3.2.4 | Complicial thinness extensions | 125  |
|  3.2.5 | Saturation extensions | 133  |
|  3.2.6 | Conclusion | 134  |
|  **3.3** | **Complicial sets as of model of $(\infty, n)$-categories** | **134**  |
|  3.3.1 | The case $n < \omega$ | 134  |
|  3.3.2 | The case $n = \omega$ | 138  |

Results of Gagna, Harpaz et Lanari ([GHL22]) states that 2-complicial sets are a model of $(\infty, 2)$-categories. The purpose of this chapter is to generalize this result to any $n \in \mathbb{N} \cup \{\omega\}$.

The heart of the proof corresponds to constructing a Quillen adjunction between complicial sets and Segal precategories enriched in a model category $A$. We begin with the study (stratified) $A$-Segal categories. We then introduce the concept of *complicial Gray module* (definition 3.1.5.4). In short, a model category $A$ is a complicial Gray module when it admits a *Gray $\circ$-cylinder* $C \mapsto I \otimes C$ and a *Gray op-cone* $C \mapsto e \star C$, and when the assignment $[n] \rightarrow e \star e \star \dots e \star \emptyset$ lifts to a Quillen adjunction with stratified simplicial sets endowed with the model structure for complicial sets.

We then prove the following stability result:

101