3.1. PRELIMINARIES

### 3.1.5 Complicial Gray module

Construction 3.1.5.1. Let $A$ be a Gray module and $a$ an object of $A$. We define $e \star a$ as the pushout:

$$\begin{array}{c} \{0\} \times a \longrightarrow [1] \otimes a \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \longrightarrow e \star a \end{array}$$

We consider the natural transformations $s^0 \star a : e \star e \star a \to e \star a$ and $d^0 \star a : a \to e \star a$, induced respectively by the morphism

$$\begin{array}{rcl} [1] \otimes [1] \otimes a & \to & ([1] \times [1]) \otimes a \quad \to \quad [1] \otimes a \\ & & (\{i\} \times \{j\}) \otimes a \mapsto \{i \wedge j\} \otimes a. \end{array}$$

and the morphism

$$\{1\} \otimes a \to [1] \otimes a.$$

These natural transformations induce commutative diagrams:

$$\begin{array}{c} e \star e \star e \star a \xrightarrow{s^0 \star (e \star a)} e \star e \star a \\ e \star (s^0 \star a) \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star e \star a \xrightarrow{s^0 \star a} e \star a \end{array}$$

$$\begin{array}{c} e \star a \xrightarrow{e \star d^0} e \star e \star a \xrightarrow{d^0 \star (e \star a)} e \star a \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ id \longrightarrow e \star a \xleftarrow{id} \end{array}$$

The (inverted) composition $g, f \mapsto g \circ f$ is a monoidal structure on the category of endomorphisms of $A$ and the natural transformation $s^0 : e \star e \star \_ \to e \star \_ \}}$ defines a structure of monoid for $e \star \_$. This induces a functor $\Delta \times A \to A$ sending $([n], a)$ to $e \star e \star \dots \star a$. We extend this to a functor $\Delta_t \times A \to A$ in defining $[n]_t \star a$ as the pushout:

$$\begin{array}{c} \coprod_{k \ge -1} \coprod_{b, \tau_k^i(b)=b} \coprod_{b \to a} [n] \star b \longrightarrow [n] \star a \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{k \ge -1} \coprod_{b, \tau_k^i(b)=b} \coprod_{b \to a} \tau_{n+k}^i([n] \star b) \longrightarrow [n]_t \star a \end{array}$$

where $\tau_{-1}^i$ is the constant functor with value $\emptyset$.

By left Kan extension, this gives a colimit preserving functor

$$\operatorname{tPsh}(\Delta) \times \operatorname{tSeg}(A) \to \operatorname{tSeg}(A). \tag{3.1.5.2}$$

and evaluated on the empty Segal $A$-category, a colimit preserving functor

$$\operatorname{tPsh}(\Delta) \to \operatorname{tSeg}(A). \tag{3.1.5.3}$$

Definition 3.1.5.4. A Gray module $A$ is a complicial Gray module if

- (1) For any $a$, the morphisms $\Lambda^1[2] \star a \to [2]_t \star a$ and $\{\epsilon\} \star a \to [1]_t \star a$ with $\epsilon \in \{-, +\}$ are acyclic cofibrations.
- (2) The functor $\operatorname{tPsh}(\Delta)^\omega \to \operatorname{tSeg}(A)$ defined in (3.1.5.3) is a left Quillen functor where $\operatorname{tPsh}(\Delta)^\omega$ denotes the model structure for $\omega$-complicial sets given in theorem 2.2.1.8.

Remark 3.1.5.5. In general, $[n] \otimes e$ and $[n] \star \emptyset$ are two very different objects. Indeed $[n] \otimes e$ has to be invariant up to homotopy under $\tau_1^i$ which is not the case for $[n] \star \emptyset$. Analogously $[k] \otimes ([l] \otimes [a])$ and $([k] \otimes [l]) \otimes [a]$ have a priori no links.

113