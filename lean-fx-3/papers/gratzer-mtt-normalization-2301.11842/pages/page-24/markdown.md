27:24

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

**Remark 5.2.** One may explicitly present $\mathbf{Gl}(\mathbf{i}[m]^*)$ as a presheaf category over the *collage* of $\mathsf{Ren}_m$ and $\mathsf{Cx}_m$ [CJ95]. This is a category whose objects are given by the disjoint union of $\mathsf{Ren}_m \coprod \mathsf{Cx}_m$ and with morphisms defined as follows:

$$\begin{array}{l} [\iota_0(\Delta), \iota_0(\Gamma)] = [\Delta, \Gamma]_{\mathsf{Ren}_m} \quad [\iota_1(\Delta), \iota_1(\Gamma)] = [\Delta, \Gamma]_{\mathsf{Cx}_m} \\ [\iota_1(\Delta), \iota_0(\Gamma)] = [\Delta, i(\Gamma)]_{\mathsf{Cx}_m} \quad [\iota_0(\Delta), \iota_1(\Gamma)] = \emptyset \end{array}$$

As a further consequence of Theorem 4.17, the projection map $\pi_0 : \mathcal{G} \longrightarrow \mathcal{S}$ is a morphism of cosmoi. In this section, we equip $\mathcal{G}$ with the structure of an MTT cosmos and show that $\pi_0$ extends to a morphism of MTT cosmoi.

**5.1. Prerequisites for the normalization cosmos.** Before we extend $\mathcal{G}$ to an MTT cosmos, we import features of $\mathcal{G}$ into the language of MSTC to specialize the latter to this situation. In this section, we begin using the interpretation of MTT to work internally to $\mathcal{G}$ and explicitly record the extensions to MSTC required for the normalization proof.

**Notation 5.3** (Dependent open modality). As $\bigcirc A = \mathbf{syn} \to A$, we will write $\bigcirc_z A(z) = (z : \mathbf{syn}) \to A(z)$ for the *dependent* version of the open modality.

**Notation 5.4** (Extension types). Given a type $A$, a proposition $\phi$, and an element $a : \phi \to A$, we write $\{A \mid x : \phi \mapsto a(x)\}$ for subtype of $A$ of elements equal to $a$ under $\phi$. Formally:

$$\{A \mid x : \phi \mapsto a(x)\} = \sum_{a':A} (x : \phi) \to a' = a(x)$$

We treat the coercion $\{A \mid x : \phi \mapsto a(x)\} \to A$ as silent and refer to the equation $a' = a(x)$ as a *boundary condition*.

Recall from Example 3.6 that $\mathcal{S}$ already contains the structure of an MTT cosmos. As a presheaf cosmos, this manifests through a series of constants in the internal language of $\mathcal{S}$. Using Lemma 4.5 we import these constants into $\mathcal{G}$.

**Extension 1.** *For each $m : \mathcal{M}$, there is a pair of constants $z : \mathbf{syn} \vdash \mathsf{Ty}_m(z) : \mathsf{U}_0 @ m$ and $z : \mathbf{syn}, A : \mathsf{Ty}_m(z) \vdash \mathsf{Tm}_m(z, A) : \mathsf{U}_0 @ m$. These constants are further equipped with operations à la Figure 4 closing them under dependent sums, dependent products, modal types, etc.*

Next, observe that normals, neutrals, and normal types are equipped with an action by renamings, so that they can be structured as presheaves over $\mathsf{Ren}_-$. The decoding operations further organize them into proof-relevant predicates over terms and types e.g., the presheaf of normal types as an object of $\mathcal{G}$ lying over the presheaf of types from $\mathcal{S}(m)$. In fact, because renamings map variables to variables, the collection of variables of a given type organizes into a presheaf over $\mathsf{Ren}_-$ and part of an object in $\mathcal{G}$. We import these objects into the internal language as additional constants:

**Extension 2.** *Given $m : \mathcal{M}$ and $A : \bigcirc_z \mathsf{Ty}_m(z)$, we have constants $\mathsf{Nf}_m(A), \mathsf{Ne}_m(A), \mathsf{V}_m(A) : \{\mathsf{U}_0 \mid z : \mathbf{syn} \mapsto \mathsf{Tm}_m(z, A(z))\}$ and $\mathsf{Nf}\mathsf{Ty}_m : \{\mathsf{U}_0 \mid z : \mathbf{syn} \mapsto \mathsf{Ty}_m(z)\}$.*

*We treat the coercion from $\mathsf{V}_m(A)$ to $\mathsf{Ne}_m(A)$ as silent.*

**Notation 5.5.** We frequently omit explicitly passing $z : \mathbf{syn}$ as an argument to $M : \bigcirc X$. For instance, given $A, B : \bigcirc \mathsf{Ty}_m$ we write $\mathsf{Nf}_m(\mathsf{Prod}(A, B))$ not $\mathsf{Nf}_m(\lambda z. \mathsf{Prod}(z, A(z), B(z)))$.