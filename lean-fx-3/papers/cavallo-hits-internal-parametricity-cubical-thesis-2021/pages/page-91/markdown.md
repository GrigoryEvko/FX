Formalism and models 79

$$\frac{\Gamma.\mathbb{I}\vdash A \text{ type} \quad \Gamma\vdash r,s:\mathbb{I} \quad \Gamma\vdash M:A[\text{id.}r]}{\text{coe}_A^{r\rightarrow s}(M):A[\text{id.}s]}$$
$$\frac{\Gamma.\mathbb{I}\vdash A \text{ type} \quad \Gamma\vdash r:\mathbb{I} \quad \Gamma\vdash M:A[\text{id.}r]}{\text{coe}_A^{r\rightarrow r}(M)=M:A[\text{id.}r]}$$

Composition is more involved, as we need a way to represent the list of terms constituting a tube. But our goal here is not to give a complete formalism for cubical type theory, only to set up enough structure to make sense of further additions in Part III. We therefore leave the remainder as an exercise to the reader and refer to [ABCFHL19; CCHM15] for more complete examples of cubical formalisms.

### 3.3.1 Models in cubical sets

The “standard” non-computational models for cubical formalisms interpret contexts as *cubical sets*, presheaves on a given *cube category*. For cartesian cubical type theory, the cube category has a simple description in terms of interval contexts. We assume some basic knowledge of category-theoretic terminology.

**Definition 3.3.1.** The *cartesian cube category* $\mathfrak{D}_c$ is the category whose objects are interval contexts $\Psi$ ictx and whose morphisms $\psi \in \mathfrak{D}_c[\Psi', \Psi]$ from $\Psi'$ to $\Psi$ are interval substitutions $\Psi' \Vdash \psi \in \Psi$.

A *presheaf* on a category $C$ is a family of sets indexed by elements of $C$, with transition functions between those sets indexed by the morphisms of $C$. More concisely, it is a functor from the opposite category of $C$ into the category of sets.

**Definition 3.3.2.** A presheaf $G$ on a category $C$ consists of the following data.

- For every $c \in C$, an set $G(c)$.
- For every $f \in C[c', c]$, a function $G(f): G(c) \rightarrow G(c')$.

We require that $G(id_c) = id_{G(c)}$ for every $c \in C$ and $G(f \circ g) = G(g) \circ G(f)$ for every $g \in C[c'', c']$ and $f \in C[c', c]$.

We write $PSh(C)$ for the category of presheaves on $C$. We define the morphisms $\alpha \in PSh(C)[G, H]$ to be families of functions $\alpha(c): G(c) \rightarrow H(c)$ satisfying a naturality condition.

**Definition 3.3.3.** A morphism $\alpha \in PSh(C)[G, H]$ is a family $\alpha(c): G(c) \rightarrow H(c)$ of functions such that $H(f) \circ \alpha(c) = \alpha(c') \circ G(f)$ for every $f \in C[c', c]$.