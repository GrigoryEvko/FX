# 6 Commutation rules 40

6.1 Substitution and substitution 40
6.2 Modality and substitution 40
6.3 Multiplier and substitution 41
6.4 Multiplier and modality 42
6.5 Multiplier and multiplier 43

# A Changelog 45

A.1 Definition 3.1.1 45
A.2 Definition 3.1.2 45
A.3 Definition 3.4.1 45
A.4 Quotient theorem 46
A.5 Definition 3.5.1 46
A.6 Definition 4.1.1 46

# 1 Introduction

The purpose of these notes is to give a categorical semantics for the transpension type [ND24], which is right adjoint to a potentially substructural dependent function type.

- In section 2 we discuss some prerequisites.
- In section 3, we define multipliers and discuss their properties.
- In section 4, we study how multipliers lift from base categories to presheaf categories.
- In section 5, we explain how typical presheaf modalities can be used in the presence of the transpension type.
- In section 6, we study commutation properties of prior modalities, substitution modalities and multiplier modalities.

# 2 Prerequisites

## 2.1 On adjoints

### 2.1.1 Adjoints and natural transformations

Lemma 2.1.1. Let $L \dashv R$.

- Natural transformations $LF \to G$ correspond to natural transformations $F \to RG$, naturally in $F$ and $G$.
- Natural transformations $FR \to G$ correspond to natural transformations $F \to GL$, naturally in $F$ and $G$.

Proof. The first statement is trivial.

To see the second statement, we send $\zeta : FR \to G$ to $\zeta L \circ F\eta : F \to GL$, and conversely $\theta : F \to GL$ to $G\varepsilon \circ \theta R : FR \to G$. Naturality is clear. Mapping $\zeta$ to and fro, we get

$$G\varepsilon \circ \zeta LR \circ F\eta R = \zeta \circ FR\varepsilon \circ F\eta R = \zeta. \tag{1}$$

Mapping $\theta$ to and fro, we get

$$G\varepsilon L \circ \theta RL \circ F\eta = G\varepsilon L \circ GL\eta \circ \theta = \theta. \tag{\square}$$

2