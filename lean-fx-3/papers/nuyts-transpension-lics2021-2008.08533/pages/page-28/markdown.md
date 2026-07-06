16:28

A. NUYTS AND D. DEVRIESE

Vol. 20:2

|  Example | Base category | Multiplier | Objectwise pointable category | Copointed/ Weakening | Exchange | Comonad/ Contraction | Cartesian | T-s. faithful | T-s. full | T-s. shard-free | T-s. right adjoint  |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
|  6.10 | W | Id | ? | ☑ | ☑ | ☑ | ☑ | ☑ | ☑ | ☑ | ☑  |
|  6.11 | W | (⊔ × U) ⊕ Id | ? | ☑ | ☑ | ☑ | ☑ | ? | ✗ | ? | ☑  |
|  6.13 | ^{a}Cube | ⊔ × (i : I) | a ≠ 0 | ☑ | ☑ | ☑ | ☑ | ☑ | ✗ | ☑ | ☑  |
|  6.14 | ^{a}Cube_{□} | ⊔ × (i : I) | a ≠ 0 | ☑ | ☑ | ✗ | ✗ | ☑ | ☑ | ☑ | ☑  |
|  6.15 | CCHM | ⊔ × (i : I) | ☑ | ☑ | ☑ | ☑ | ☑ | ☑ | ✗ | ✗ | ☑  |
|  6.16 | DCube_{d} | ⊔ × (i : (k)) | ☑ | ☑ | ☑ | ☑ | ☑ | ☑ | ✗ | ☑ | ☑  |
|  6.17 | Clock | ⊔ × (i : ⊕_{k}) | ✗ | ☑ | ☑ | ☑ | ☑ | ☑ | ✗ | ☑ | ☑  |
|  6.18 | TwCube | ⊔ × I | ☑ | ✗ | ✗ | ✗ | ✗ | ☑ | ☑ | ☑ | ☑  |
|  6.19 | n | min(⊔, i) | ✗ | ☑ | ☑ | ☑ | ☑ | ☑ | ✗ | ☑ | ☑  |
|  6.20 | ^{2}Cube_{⊥} | ⊔ × ⊥ | ☑ | ☑ | ☑ | ☑ | ☑ | ✗ | ✗ | ☑ | ☑  |

Figure 7: Some interesting multipliers and their properties. Properties that follow from being cartesian are greyed out.

**Example 6.14** (Affine cubes). Let $^a\text{Cube}_\square$ be the category of affine $a$-ary cubes as used in [BCH14] (binary) or [BCM15] (unary). It is the free semicartesian monoidal category with same terminal unit over $^a\text{RG}$. Concretely:

- • Objects are as in $^a\text{Cube}$,
- • Morphisms are as in $^a\text{Cube}$ such that if $j\langle\varphi\rangle = k\langle\varphi\rangle \notin \{0, \dots, a-1\}$, then $j = k$. This rules out diagonal maps.

This category is objectwise pointable if and only if $a \neq 0$. On this category, we consider the functor $\cup \cdot (i : \mathbb{I}) : W \mapsto (W, i : \mathbb{I})$, which is a multiplier for $(i : \mathbb{I})$. Dimensional splitness and the boundary are as in $^a\text{Cube}$. This functor is T-slice right adjoint with $\exists_{(i:\mathbb{I})}((W, j : \mathbb{I}), (j/i)) = W$ and $\exists_{(i:\mathbb{I})}(W, (\varepsilon/i)) = W$ for each of the $a$ endpoints $\varepsilon$.

In the nullary case, $^0\text{Cube}_\square$ is the base category of the Schanuel topos, a sheaf topos equivalent to the category of nominal sets [Pit13]. In that case, $\exists_{(i:\mathbb{I})}$ is not just left adjoint to $\perp_{(i:\mathbb{I})}$, but in fact an inverse and hence also right adjoint. This is in line with the fact that in nominal type theory [PMD15], there is a single name quantifier which can be read as either existential or universal quantification.

**Example 6.15** (CCHM cubes). Let CCHM be the category of CCHM cubes [CCHM17], which is objectwise pointable. Its objects are as in $^2\text{Cube}$ and its morphisms $(i_1 : \mathbb{I}, \dots, i_n : \mathbb{I}) \to (j_1 : \mathbb{I}, \dots, j_m : \mathbb{I})$ are functions from $\{j_1, \dots, j_m\}$ to the free de Morgan algebra over $\{i_1, \dots, i_n\}$. We again consider $\cup \times (i : \mathbb{I})$, another instance of Example 6.11. A slice object $(V, \varphi)$ is now (dimensionally) split if $i\langle\varphi\rangle$ is not an endpoint, so the boundary is again $\top \uplus \top$. The so-called *connections* $(j \vee k/i), (j \wedge k/i) : (j : \mathbb{I}, k : \mathbb{I}) \to (i : \mathbb{I})$ are shards, because they have sections $(i/j, 0/k) : (i : \mathbb{I}) \to (j : \mathbb{I}, k : \mathbb{I})$ and $(i/j, 1/k) : (i : \mathbb{I}) \to (j : \mathbb{I}, k : \mathbb{I})$ respectively but are not in the image of $\perp_{(i:\mathbb{I})}$.

**Example 6.16** (Depth $d$ cubes). Let DCube$_{d}$ with $d \geq -1$ be the category of depth $d$ cubes, used as a base category in degrees of relatedness [ND18a, Nuy18a]. This is a generalization of the category of binary cartesian cubes Cube, where instead of typing every dimension with