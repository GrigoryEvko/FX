Remark A.3.1 (axiom.shape). In the formal development, we do not work with cubes defined explicitly as products of an interval. Instead, we assume an abstract type Shape and a decoding function giving $\langle S\rangle:\mathcal{V}$ for each $S:\text{Shape}$. We require that the interval $\mathsf{I}$ is coded by a shape, but not that every shape is a power of $\mathsf{I}$, nor that $\mathsf{I}^n$ is coded by a shape for $n\neq 1$. To obtain the equivariant fibration model, we would instantiate with Shape := $\mathbb{N}$ and $\langle n\rangle := \mathsf{I}^n$. We can also recover the non-equivariant model by taking $\mathsf{I}$ to be the only shape.

A.4. Partial elements and contractible types. The notion of partial elements and contractible types play a crucial role in this internal description. Both definitions use only the type of cofibrations $\Phi$ and not the interval type $\mathsf{I}$.

Definition A.4.1 (cofibration.$_{-+}$). To each type $A$ we associate a type $A^{+} := \Sigma_{\psi:\Phi} A^{[\psi]}$ of partial elements of $A$. A partial element of $A$ is thus a pair $\psi, u$ where $u$ is in $A^{[\psi]}$. The operation $A \mapsto A^{+}$ on types is reflected in all universes and so defines a function $\mathcal{V} \to \mathcal{V}$.

There is a canonical injection $i_A: A \to A^{+}$ which to any $a: A$ associates the element $\top, u$ in $A^{+}$ with $u \, x := a$. Viewed externally, $i_A$ is the partial map classifier introduced in §2.2, taken relative to the ambient context.

Definition A.4.2 (fibration.trivial.Contr). For any type $A$, we can consider the type Contr($A$) of contractibility structures on $A$. This is the type of operations $c_A$ which take a partial element $\psi, u$ in $A^{+}$ and build an element $c_A(\psi, u)$ in $A$ such that $[\psi]$ implies $c_A(\psi, u) = u \, \text{tt}$.

Remark A.4.3. Any contractibility structure $c_A$ is a left inverse of $i_A$: we have $c_A(i_A \, a) = a$ for any $a$ in $A$. Maybe surprisingly, the converse also holds: any left inverse $c_A$ of $i_A$ is in Contr($A$), because if $c_A$ is a left inverse of $i_A$ then for any $\psi, u$ in $A^{+}$ we have that $[\psi]$ implies $(\psi, u) = i_A(u \, \text{tt})$ and thus $c_A(\psi, u) = c_A(i_A(u \, \text{tt})) = u \, \text{tt}$.

Definition A.4.4 (fibration.trivial.TFibStr). A trivial fibration structure on a family of types $A$ over $\Gamma$ then consists of a family of contractibility structures on $A \, \gamma$ for each $\gamma: \Gamma$.

Viewed externally, such a family corresponds to a uniform trivial fibration structure in the sense of Definition 2.2.9.

A.5. Filling and equivariant filling. Next we finish defining the interpretation of types by defining equivariant filling structures. We first generalize the definition of fibration used by Angiuli et al. [ABCHFL21], replacing the interval by an arbitrary type.

Definition A.5.1 (fibration.fibration.LocalFillStr). Let $S$ be a type and $A$ be a family of types over $S$; we define the type LocalFill$_S$ $A$ of local $S$-filling structures on $A$. These are operations $c_A$ which take as argument $r_0: S$ and $a_0: A \, r_0$ and a partial section $\psi, u: (\Pi_{r:S} A \, r)^{+}$ compatible with $a_0$, i.e. such that $[\psi]$ implies $u \, \text{tt} \, r_0 = a_0$, and produce an element $c_A \, r_0 \, a_0 \, (\psi, u)$ in $\Pi_{r:S} A \, r$ which extends $\psi, u$ and such that $c_A \, r_0 \, a_0 \, (\psi, u) \, r_0 = a_0$.

Definition A.5.2 (fibration.fibration.FillStr). Let $S$ be a type and $A$ be a family of types over $\Gamma$. An $S$-filling structure $c_A$ on $A$ consists of a local $S$-filling structure $c_A \, \gamma: \text{LocalFill}_S \, (A \circ \gamma)$ for every $\gamma: \Gamma^S$. We write Fill$_S$ $A$ for the type of $S$-filling structures on $A$.

In the cartesian cubical set model of Angiuli et al. [ABCHFL21], a type is a family paired with an $\mathsf{I}$-filling structure. To define equivariant filling structures, we use the case where $S = \mathsf{I}^n$ for some $n: \mathbb{N}$. In this case the symmetric group $\Sigma_n$ acts in a canonical way on $S$. It then acts on $\Gamma^S$ by precomposition, with $\gamma \sigma := \gamma \circ \sigma$ for $\gamma: \Gamma^S$ and $\sigma: \Sigma_n$. We likewise have an action on partial elements: given $(\psi, u): (\Pi_{r:S} A \, r)^{+}$ define $(\psi, u) \sigma: (\Pi_{r:S} A \, (\sigma \, r))^{+}$ by $(\psi, u) \sigma := (\psi, u')$ where $u' \, x \, r := u \, x \, (\sigma \, r)$ for $x: [\psi]$ and $r: S$.

78