122

General higher inductive types

Definition 6.2.2 (Syntactic interpretation of types and contexts). Let a telescope $\Delta$, specification $\mathcal{K}$, argument context $\Theta$, and argument type $\mathfrak{B}$ be given. Let $\chi$ be an instantiation for the variables in $\Theta$. We define the syntactic interpretation of $\mathfrak{B}$ at $\chi$, written $(\Theta.\mathfrak{B})_\mathcal{K}^\Delta(\chi)$, as follows.

$$(\Theta.\text{IND}(\delta))_\mathcal{K}^\Delta(\chi) := \text{Ind}_\mathcal{K}^\Delta(\delta)$$

$$(\Theta.(b:B) \to c)_\mathcal{K}^\Delta(\chi) := (b:B) \to (\Theta.c)_\mathcal{K}^\Delta(\chi)$$

$$(\Theta.\text{PATH}(x.\mathfrak{B},\mathfrak{M}_0,\mathfrak{M}_1))_\mathcal{K}^\Delta(\chi) := \text{Path}(x.(\Theta.\mathfrak{B})_\mathcal{K}^\Delta(\chi), M_0, M_1)$$

$$\text{where } M_\varepsilon := (\Theta.\mathfrak{M}_\varepsilon)_\mathcal{K}(\chi) \text{ for } \varepsilon \in \{0, 1\}$$

We define a telescope $(\Theta)_\mathcal{K}^\Delta$, the syntactic interpretation of $\Theta$, as follows.

$$(\cdot)_\mathcal{K}^\Delta := \cdot$$

$$(\Theta, a:\mathfrak{A})_\mathcal{K}^\Delta := (\Theta)_\mathcal{K}^\Delta, a: (\Theta.\mathfrak{A})_\mathcal{K}^\Delta(\bar{v}_{(\Theta)_\mathcal{K}^\Delta})$$

### 6.2.2 Relational interpretation

Next, we have a second interpretation of argument types and contexts as operators on indexed relations. Given a specification $\Psi \Vdash \Delta \blacktriangleright \mathcal{K}$ spec and $(\Psi, \Delta)$-relation $R$, we can interpret any argument type $\Psi \Vdash \Delta \mid \mathcal{K} \mid \cdot \blacktriangleright \mathfrak{A}$ atype as a $\Psi$-relation by interpreting instances of $\text{IND}(-)$ with $R$ and interpreting compound types by their usual relational definitions. (Recall that we defined $\Gamma$-relations for arbitrary contexts $\Gamma$ in Definition 3.1.25).

First, we define some notation for the function and path type formers as relational operators, following the definitions in Sections 2.1.4 and 3.1.5 respectively.

Definition 6.2.3. Given a term $A$ and $(\Psi, a:A)$-relation $R$, we define a $\Psi$-relation $Fun(A, R)$ for $\Psi' \Vdash \psi \in \Psi$ as follows.

$$V \approx V' \in Fun(A, R)\langle\psi\rangle : \Longleftrightarrow \begin{cases} V = \lambda a. N \text{ and } V = \lambda a. N' \text{ with} \\ \Psi', a: A\psi \gg N \approx N' \in \Downarrow R(\psi, a/a) \end{cases}$$

Definition 6.2.4. Given a $(\Psi, x:\mathbb{I})$-relation $R$ and terms $M_0$ and $M_1$, we define a $\Psi$-relation $Path(R, M_0, M_1)$ for $\Psi' \Vdash \psi \in \Psi$ as follows.

$$V \approx V' \in Path(R, M_0, M_1)\langle\psi\rangle : \Longleftrightarrow \begin{cases} V = \lambda^\mathbb{I}x. M \text{ and } V = \lambda^\mathbb{I}x. M' \text{ with} \\ M \approx M' \in \Downarrow R(\psi, x/x) \text{ and} \\ M[\varepsilon/x] \approx M_\varepsilon\psi \in \Downarrow R(\psi, \varepsilon/x) \text{ for } \varepsilon \in \{0, 1\} \end{cases}$$

These components then assemble straightforwardly into an interpretation of argument types and contexts.