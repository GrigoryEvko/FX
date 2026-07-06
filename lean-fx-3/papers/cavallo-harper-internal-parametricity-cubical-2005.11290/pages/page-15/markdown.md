Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:15

A and B[0/x], their V-type fits into the following (“V-shaped”) diagram.

$$\begin{array}{c} A \\ I \downarrow \\ B_0 \xrightarrow{} B \\ x \to \end{array} \xrightarrow{} B_1$$

Rules for V-types are shown in Figure 3. We convert isomorphisms to paths in the universe by applying V with a degenerate path.

$$\frac{A \in \mathcal{U} \quad B \in \mathcal{U} \quad I \in \text{Iso}(A, B)}{\text{ua}(A, B, I) := \lambda^{\mathbb{I}} x . \mathsf{V}_x(A, B, I) \in \text{Path}_{\mathcal{U}}(A, B)}$$

Here, x does not appear in B, so we are composing the isomorphism I with the reflexive path ...B. This reflexive path corresponds to the identity isomorphism on B, so when we pre-compose with I we simply get a path corresponding to I.

We will not be using V-types directly in the future, only the univalence axiom that they enable. Rather, we introduce them here in order to make a comparison with their parametric equivalent in Section 2.4. For that purpose, let us give some intuition as to why V is formulated as it is. Univalence involves a “dimension shift”: it takes a point in the type of isomorphisms and produces a path in the universe, which is an element one dimension higher. However, we cannot impose in the typing rule for $\mathsf{V}_x(A, B, I)$ that A, B, I live “one dimension lower,” i.e., are degenerate in x, because this property is not stable under substitution. For example, mod(M, x) may be degenerate in some y, but mod(M, x)[y/x] is certainly not degenerate in y[y/x]. All aspects of type theory should be stable under substitution, so this is a non-starter. Instead, we structure $\mathsf{V}_r$ in such a way that it does not involve a dimension shift; both the input and the output vary in the direction r.

1.5. Higher inductive types. Finally, cubical type theory can include a variety of higher inductive types. These can be seen as a mutual generalization of inductive types and quotients; they are inductive definitions that permit path constructors in addition to ordinary constructors.

It is beyond the scope of this work to give a comprehensive account of higher inductive types in cartesian cubical type theory; for that, we refer to [CH19a]. We will instead go by way of example, expanding on the type $\mathbb{Z}/2\mathbb{Z}$ of integers mod 2 specified in the introduction.

data $\mathbb{Z}/2\mathbb{Z}$ where

| in(n : $\mathbb{Z}$) $\in \mathbb{Z}/2\mathbb{Z}$

| mod(n : $\mathbb{Z}$, x : $\mathbb{I}$) $\in \mathbb{Z}/2\mathbb{Z}$ [x = 0 $\hookrightarrow$ in(n) | x = 1 $\hookrightarrow$ in(n + 2)]

The mod constructor exemplifies the format of a path constructor: it takes one or more interval variables as arguments, and it has a specified boundary which can refer to its arguments and previous construtors. This specification indicates the following introduction and boundary rules for in and mod.

$$\frac{\Gamma \gg N \in \mathbb{Z}}{\Gamma \gg \text{in}(N) \in \mathbb{Z}/2\mathbb{Z}}$$

$$\frac{\Gamma \gg N \in \mathbb{Z} \quad \Gamma \gg r \in \mathbb{I}}{\Gamma \gg \text{mod}(N, r) \in \mathbb{Z}/2\mathbb{Z}}$$

$$\frac{\Gamma \gg N \in \mathbb{Z}}{\Gamma \gg \text{mod}(N, 0) = \text{in}(N) \in \mathbb{Z}/2\mathbb{Z}}$$

$$\frac{\Gamma \gg N \in \mathbb{Z}}{\Gamma \gg \text{mod}(N, 1) = \text{in}(N + 2) \in \mathbb{Z}/2\mathbb{Z}}$$