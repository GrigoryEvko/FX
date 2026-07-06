modern algebra and mathematics. For an introduction we refer the reader to books by Awodey [Awo10] and Mac Lane [Mac78].

It is instructive to try to encode a very simple modal syntax as a mode theory. Recall that traditional modal logics assume a single-mode syntax. Thus, we define the set $\mathcal{M}_{\mathbf{K}} = \{\bullet\}$ to consist of a unique mode $\bullet$. Next, we can generate the morphisms by stipulating that $\square : \bullet \rightarrow \bullet$ is an endomodality on that unique mode. We can then generate the *free category* based on this data. This is essentially the free monoid on a set of generating morphisms, subject to the restriction that in any string of morphisms the target of a morphism always matches the source of the next. As this happens trivially in our case (we have a unique mode), the set of morphisms is exactly the free monoid on one generator: its elements consist of the modalities $\square^n : \bullet \rightarrow \bullet$ for each $n \in \mathbb{N}$. The composite of two morphisms is

$$\square^a \circ \square^b = \square^{a+b}$$

Finally, the identity morphism for this operation is $\square^0$.

This generates a syntax with an infinite set of modalities: if $\varphi \circledast \bullet$ then

$$\langle \square^0 \mid \varphi \rangle, \langle \square \mid \varphi \rangle, \langle \square^2 \mid \varphi \rangle, \dots \circledast \bullet$$

are all well-formed formulas at mode $\bullet$. We will see later that the logic generated here is essentially (an intuitionistic variant of) the smallest normal modal logic $\mathbf{K}$ [BRV01, §1.6].

### 2.3. Transformations between modalities

This technology does not suffice to encode richer settings. For example, the 4 axiom

$$\square \phi \rightarrow \square \square \phi$$

is one of the two a characteristic axioms of the modal logic $\mathbf{S4}$ [HC96, §3]. We would ideally like to be able to encode this as part of the structure of the mode theory $\mathcal{M}$. However, none of the 'moving parts' of $\mathcal{M}$ allows the representation of such information.

Consequently, to encode implications such as the above we will need to add another layer to the mode theory $\mathcal{M}$. We will postulate that between any two 'parallel' modalities $\mu, \nu : n \rightarrow m$ with the same source and target mode there exists a set of *transformations*

$$\alpha : \mu \Rightarrow \nu$$

These transformations—typically denoted by letters $\alpha, \beta, \dots$—encode implications between modalities. We are likely to collectively call the modes $m, n$ and the modalities $\mu$ and $\nu$ the *boundary* of $\alpha$.

The presence of such a transformation in $\mathcal{M}$ will allow us to prove the formula

$$\langle \mu \mid \varphi \rangle \rightarrow \langle \nu \mid \varphi \rangle \circledast m$$

in the logic, for any formula $\varphi \circledast n$. For example, if in $\mathcal{M}_{\mathbf{K}}$ we postulate a transformation

$$4 : \square \Rightarrow \square^2$$

4