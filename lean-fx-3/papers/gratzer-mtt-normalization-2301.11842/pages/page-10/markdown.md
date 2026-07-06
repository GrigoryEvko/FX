27:10

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

$$f \circledast a = \text{let } \text{mod}_{\mu}(f_0) \leftarrow f \text{ in let } \text{mod}_{\mu}(a_0) \leftarrow a \text{ in } \text{mod}_{\mu}(f_0(a_0))$$

In functional programming parlance, modalities are *applicative functors* though without an operation $A \to \langle \mu \mid A \rangle$ [MP08].

While it is far less useful, one can also define a version of $\circledast$ using the modalized dependent product rather than accepting elements of $\langle \mu \mid - \rangle$:

$$(\circledast') : (\mu \mid (x : A) \to B(x)) \to (\mu \mid a : A) \to \langle \mu \mid B(a) \rangle$$

$$f \circledast' a = \text{mod}_{\mu}(f(a))$$

This is indicative of a common pattern; it is typically far more concise to use the modalized dependent product instead of accepting $\langle \mu \mid - \rangle$ in order to avoid needing to immediately eliminate arguments.

2.4. **Normal and neutral forms in MTT.** As mentioned in Section 1.2, the starting point for normalization is the definition of normal form. In MTT—as in other type theories—normal forms are presented together with a class of neutral forms. Intuitively, normal forms capture terms in $\beta$-normal and $\eta$-long form while neutrals are chains of eliminations applied to a variable.

We define normal and neutral forms as separate syntactic classes, equipped with their own family of typing judgments and decoding functions sending them to terms. Dependency complicates this definition as various typing rules require substitution in the types of premises or the conclusion. Unfortunately, it is just as hard to define substitution on normal forms as it is to define normalization in general [WCPW04]. Accordingly, a normal form (resp. neutral, normal type) is typed by the judgment $\Gamma \vdash^{\text{ref}} u : A \circledast m$ (resp. $\Gamma \vdash^{\text{rev}} e : A \circledast m$, $\Gamma \vdash^{\text{ref}} \tau \circledast m$) where $A$ is not required to be any sort of normal form. Furthermore, these judgments are defined inductive-recursively with decoding functions $|u|$ (resp. $|e|$, $|\tau|$) which send a normal form (resp. neutral, normal type) to its corresponding piece of syntax. Normal and neutral forms for mode-local connectives are unchanged from their standard presentation in type theory:

$$\begin{array}{l} (\text{Normals}) \quad u ::= \lambda(u) \mid \text{up}(e) \mid \text{mod}_{\mu}(u) \mid \dots \\ (\text{Neutral}) \quad e ::= \mathbf{v}_k^{\alpha} \mid e(u) \mid \text{letmod}(\mu; \nu; \tau; e; u) \mid \dots \\ (\text{Normal types}) \quad \tau ::= (\mu \mid \tau) \to \sigma \mid \langle \mu \mid \tau \rangle \mid \text{El}(u) \mid \dots \end{array}$$

We defer a more complete presentation of the judgments and decoding function to Figure 3, but remark that the neutral form for variables is annotated with a 2-cell and index, decoding to $\mathbf{v}_0$ together with a combination of weakening and 2-cell substitutions $\uparrow$ and $\{\alpha\}$. Note that we require that $\text{El}(-)$ commute with type formers only up to isomorphism (weak Tarski universes) we must include neutral and normal forms for e.g., $\text{El}(\langle \mu \mid A \rangle)$ as well as other type connectives. We include only those for $\langle \mu \mid - \rangle$ as they are representative of the general pattern.

To ensure that normal forms are $\eta$-long, neutrals can only be 'injected' into normals by $\text{up}(-)$ for types without an $\eta$ law e.g., at modal types but not at dependent products. Finally, we emphasize that normal forms are freely generated so their equality is decidable if equality of modalities and 2-cells is decidable. This is more subtle than it may appear at first blush, and we return to this point in Section 6.2.