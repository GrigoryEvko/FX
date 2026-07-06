272

Programming in cohesive parametric type theory

Proof. We have an element P of the bridge type defined as follows.

$$P := \lambda^{\mathbf{I}} \mathbf{x} \cdot \text{mod}(\text{split}_x(\text{unmod}(c_0), \text{unmod}(c_1))) \in \text{Bridge}(\text{Codisc}(A), c_0, c_1) \text{ @ par}$$

Note that we type split in the context $((glo \mid A : U), c_0, c_1 : \text{Codisc}(A), \mathbf{x} : \mathbf{I}) \cdot glo$, with the application of glo brought about by the introduction rule for the codiscrete type. The global modality transforms the hypothesis $\mathbf{x} : \mathbf{I}$ into $\mathbf{x} : 2$, enabling us to analyze it with split.

We prove uniqueness of $P$ in a similar fashion. For any $q : \text{Bridge}(\text{Codisc}(A), c_0, c_1)$, we define a path $S \in \text{Path}(\text{Bridge}(\text{Codisc}(A), c_0, c_1), q, P)$ @ par from $q$ to $P$ as follows.

$$\lambda^{\mathbb{I}} y \cdot \lambda^{\mathbf{I}} \mathbf{x} \cdot \text{mod}(\text{split}_x(\lambda^{\mathbb{I}}_{-} \cdot \text{unmod}(c_0), \lambda^{\mathbb{I}}_{-} \cdot \text{unmod}(c_1)) y)$$

Here we are applying split at a path type like so.

$$\text{split}_x(\lambda^{\mathbb{I}}_{-} \cdot \text{unmod}(c_0), \lambda^{\mathbb{I}}_{-} \cdot \text{unmod}(c_1)) \in \text{Path}(A, \text{unmod}(q \mathbf{x}), \text{unmod}(P \mathbf{x})) \text{ @ par}$$

That is, we know that $\text{unmod}(q \mathbf{x})$ and $\text{unmod}(P \mathbf{x})$ agree for any $\mathbf{x} : 2$ by virtue of their endpoint equations, and it follows by nature of the codiscrete type that $q \mathbf{x}$ and $P \mathbf{x}$ agree for any $\mathbf{x} : \mathbf{I}$.

### 15.4 Iterated smash products

We now return to the showcase result of Part III, the characterization of polymorphic pointed functions between smash products (Section 10.5). We see that given commutator and associator functions defined in the parametric mode, we can derive pointwise functions that are guaranteed by parametricity to satisfy various coherence properties.

**Preliminaries** It will pay at this point to develop a more structured toolkit for deriving shadows of parametric functions. First, we introduce shorthand notation for instantiating a parametrically polymorphic function at a discrete type; we also here shift attention from types to pointed types.

**Definition 15.4.1.** Given a pointwise pointed type $(\text{cc} \mid A_* : U_*)$, we define its discrete embedding as $\text{Disc}_*(A_*) := \langle \text{Disc}(A), \text{mod}(a_0) \rangle \in U_* \text{ @ par}$.

**Notation 15.4.2.** Given $X : U_* \gg B$ type @ par, a function $f : (X : U_*) \to B$, and a type $(\text{cc} \mid A : U_*)$, we define $f \triangleleft A_* := f(\text{Disc}_*(A_*)) \in B[\text{Disc}_*(A)/X] \text{ @ pt}$.

Let us also explicitly define identity and composition of pointed functions.