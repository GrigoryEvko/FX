5:14

E. CAVALLO AND R. HARPER

Vol. 17:4

V-FORM

$$\frac{\Gamma, r = 0 \gg A \text{ type} \quad \Gamma \gg B \text{ type} \quad \Gamma, r = 0 \gg I \in \text{Iso}(A, B)}{\Gamma \gg V_r(A, B, I) \text{ type}}$$

V-FORM-$\partial_0$

$$\frac{\Gamma \gg A \text{ type} \quad \Gamma \gg B \text{ type} \quad I \in \text{Iso}(A, B)}{\Gamma \gg V_0(A, B, I) = A \text{ type}}$$

V-FORM-$\partial_1$

$$\frac{\Gamma \gg B \text{ type}}{\Gamma \gg V_1(A, B, I) = B \text{ type}}$$

V-INTRO

$$\frac{\Gamma, r = 0 \gg M \in A \quad \Gamma \gg N \in B \quad \Gamma, r = 0 \gg \text{fst}(I)(M) = N \in B}{\Gamma \gg \text{vin}_r(M, N) \in V_r(A, B, I)}$$

V-INTRO-$\partial_0$

$$\frac{\Gamma \gg M \in A \quad \Gamma \gg N \in B \quad \Gamma \gg \text{fst}(I)(M) = N \in B}{\Gamma \gg \text{vin}_0(M, N) = M \in A}$$

V-INTRO-$\partial_1$

$$\frac{\Gamma \gg N \in B}{\Gamma \gg \text{vin}_1(M, N) = N \in B}$$

V-ELIM

$$\frac{\Gamma \gg P \in V_r(A, B, I)}{\Gamma \gg \text{vproj}_r(P, I) \in B}$$

V-ELIM-$\partial_0$

$$\frac{\Gamma \gg P \in A \quad I \in \text{Iso}(A, B)}{\Gamma \gg \text{vproj}_0(P, I) = \text{fst}(I)(P) \in B}$$

V-ELIM-$\partial_1$

$$\frac{\Gamma \gg P \in B}{\Gamma \gg \text{vproj}_1(P, I) = P \in B}$$

Figure 3: Rules for V-types. See [Ang19] for $\beta$- and $\eta$-rules.

**Definition 1.4.** Let a function $F \in A \to B$ be given. The types $\text{Linv}(A, B, F)$ and $\text{Rinv}(A, B, F)$ of left and right inverses to $F$ are defined as follows.

$$\text{Linv}(A, B, F) := (g : B \to A) \times ((a : A) \to \text{Path}_A(g(Fa), a))$$

$$\text{Rinv}(A, B, F) := (g : B \to A) \times ((b : B) \to \text{Path}_B(F(gb), b))$$

We say $F$ is an isomorphism when it is equipped with a left and right inverse.

$$\text{islso}(A, B, F) := \text{Linv}(A, B, F) \times \text{Rinv}(A, B, F)$$

The type of isomorphisms between $A$ and $B$ is then $\text{Iso}(A, B) := (f : A \to B) \times \text{islso}(A, B, f)$.

Isomorphisms are frequently known as *equivalences* in the literature on univalent type theory. There are several isomorphic formulations of the type $\text{Iso}(A, B)$; we refer to [Uni13, Chapter 4] for more details. (Our definition is there called a *bi-invertible map*). A key property of $\text{islso}(A, B, F)$ is that it is a proposition in the following sense [Uni13, Theorem 4.3.2].

**Definition 1.5.** *A* type is a *proposition* if any two elements of $A$ are equal up to a path, as captured by the following type.

$$\text{isProp}(A) := (a : A) (b : A) \to \text{Path}_A(a, b)$$

While the V-type is used principally to convert isomorphisms to paths, it is a bit more general: it takes a path and an isomorphism and composes them to produce a new path. That is, if we have a path of types $B$ in a direction $x$ and an isomorphism $I$ between some