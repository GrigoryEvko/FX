## 2.2 Dependent ends and co-ends

We will use $\forall$ and $\exists$ to denote ends and co-ends as well as their dependent generalizations [Nuy20, §2.2.6-7]:

**Definition 2.2.1.** A **dependent end** of a functor $F : \text{Tw}(\mathcal{I}) \rightarrow \mathcal{C}$, somewhat ambiguously denoted $\forall i.F(i \xrightarrow{\text{id}} i)$, is a limit of $F$.

**Definition 2.2.2.** A **dependent co-end** of a functor $F : \text{Tw}(\mathcal{I})^{\text{op}} \rightarrow \mathcal{C}$, somewhat ambiguously denoted $\exists i.F(i \xrightarrow{\text{id}} i)$, is a colimit of $F$.

**Example 2.2.3.** Assume a functor $G : \mathcal{C} \rightarrow \mathcal{D}$. One way to denote the set of natural transformations $\text{Id}_\mathcal{C} \rightarrow \text{Id}_\mathcal{C}$ which map to the identity under $G$, is as

$$A := \forall (c \in \mathcal{C}). \{\chi : c \rightarrow c \mid G\chi = \text{id}_{Gc}\}.$$

In order to read the above as a dependent end, we must find a functor $G : \text{Tw}(\mathcal{C}) \rightarrow \text{Set}$ such that $G(c \xrightarrow{\text{id}} c) = \{\chi : c \rightarrow c \mid G\chi = \text{id}_{Gc}\}$. Clearly every covariant occurrence of $c$ refers to the codomain of $(c \xrightarrow{\text{id}} c)$, whereas every contravariant occurrence refers to the domain. So when we apply $G$ to a general object $(x \xrightarrow{\varphi} y)$ of $\text{Tw}(\mathcal{C})$, we should substitute $x$ for every contravariant $c$ and $y$ for every covariant $c$. We can then throw in $\varphi$ wherever this is necessary to keep things well-typed, as $\varphi$ disappears anyway when $(x \xrightarrow{\varphi} y) = (c \xrightarrow{\text{id}} c)$. Thus, we get

$$G(x \xrightarrow{\varphi} y) = \{\chi : x \rightarrow y \mid G\chi = G\varphi\}.$$

So we see that using a *dependent* end was necessary in order to mention $\text{id}_c$, as this generalizes to $\varphi : x \rightarrow y$ to which we do not have access in a non-dependent end.

An element of $\nu \in A$ is then a function

$$\nu : (c \in \mathcal{C}) \rightarrow \{\chi : c \rightarrow c \mid G\chi = \text{id}_{Gc}\}$$

such that, whenever $\varphi : x \rightarrow y$, we have $\varphi \circ \nu_x = \nu_y \circ \varphi$.

## 2.3 Presheaves

### 2.3.1 Notation

We use the presheaf notations from [Nuy18]. Concretely:

- The application of a presheaf $\Gamma \in \widehat{\mathcal{W}}$ to an object $W \in \mathcal{W}$ is denoted $W \Rightarrow \Gamma$.
- The restriction of $\gamma : W \Rightarrow \Gamma$ by $\varphi : V \rightarrow W$ is denoted $\gamma \circ \varphi$ or $\gamma\varphi$.
- The application of a presheaf morphism $\sigma : \Gamma \rightarrow \Delta$ to $\gamma : W \Rightarrow \Gamma$ is denoted $\sigma \circ \gamma$ or $\sigma\gamma$.
  - By naturality of $\sigma$, we have $\sigma \circ (\gamma \circ \varphi) = (\sigma \circ \gamma) \circ \varphi$.
- If $\Gamma \in \widehat{\mathcal{W}}$ and $T \in \text{Ty}(\Gamma)$ (also denoted $\Gamma \vdash T$ type), i.e. $T$ is a presheaf over the category of elements $\mathcal{W}/\Gamma$, then we write the application of $T$ to $(W, \gamma)$ as $(W \triangleright T[\gamma])$ and $t \in (W \triangleright T[\gamma])$ as $W \triangleright t : T[\gamma]$.
  - By definition of type substitution in a presheaf CwF, we have $(W \triangleright T[\sigma][\gamma]) = (W \triangleright T[\sigma\gamma])$
- The restriction of $W \triangleright t : T[\gamma]$ by $\varphi : (V, \gamma \circ \varphi) \rightarrow (W, \gamma)$ is denoted as $W \triangleright t \langle \varphi \rangle : T[\gamma\varphi]$.
- If $t \in \text{Tm}(\Gamma, T)$ (also denoted $\Gamma \vdash t : T$), then the application of $t$ to $(W, \gamma)$ is denoted $V \triangleright t[\gamma] : T[\gamma]$.
  - The naturality condition for terms is then expressed as $t[\gamma] \langle \varphi \rangle = t[\gamma\varphi]$.

4