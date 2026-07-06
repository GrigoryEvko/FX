68

Cubical type theory

Proof. By Lemma 3.1.36, we have that $P \Downarrow V$ with $\Psi \Vdash P = V \in \text{Path}(x.A, M_0, M_1)$. By the elimination rule already proven, we know $\Psi \Vdash P \varepsilon = V \varepsilon \in A[\varepsilon/x]$. Moreover, $V$ is of the form $\lambda^{\mathbb{I}}x.M$ with $\Psi, x:\mathbb{I} \Vdash M \in A$ and $\Psi \Vdash M[\varepsilon/x] = M_{\varepsilon} \in A[\varepsilon/x]$. By path reduction, we then have $\Psi \Vdash V \varepsilon = M[\varepsilon/x] \in A[\varepsilon/x]$. We obtain the result by concatenating $P \varepsilon = V \varepsilon$, $V \varepsilon = M[\varepsilon/x]$, and $M[\varepsilon/x] = M_{\varepsilon}$. $\square$

Finally, the uniqueness rule follows in much the same way.

# Rule 3.1.44 (Path uniqueness).

$$\frac{\Psi, x:\mathbb{I} \Vdash A \text{ type } \quad (\forall \varepsilon) \Psi \Vdash M_{\varepsilon} \in A[\varepsilon/x] \quad \Psi \Vdash P \in \text{Path}(x.A, M_0, M_1)}{\Psi \Vdash P = \lambda^{\mathbb{I}}x.Px \in \text{Path}(x.A, M_0, M_1)}$$

Proof. By Lemma 3.1.36, we have that $P \Downarrow \lambda^{\mathbb{I}}x.M$ with $\Psi, x:\mathbb{I} \Vdash M \in A$ and $\Psi \Vdash M[\varepsilon/x] = M_{\varepsilon} \in A[\varepsilon/x]$ for $\varepsilon \in \{0,1\}$; by weakening and path elimination, we know $\Psi, x:\mathbb{I} \Vdash Px = (\lambda^{\mathbb{I}}x.M)x \in A$. Path reduction then gives $x:\mathbb{I} \Vdash (\lambda^{\mathbb{I}}x.M)x = M \in A$, so by transitivity $x:\mathbb{I} \Vdash Px = M \in A$. Applying path introduction, we get $\Psi \Vdash \lambda^{\mathbb{I}}x.Px = \lambda^{\mathbb{I}}x.M \in \text{Path}(x.A, M_0, M_1)$, which combined with $\Psi \Vdash P = \lambda^{\mathbb{I}}x.M \in \text{Path}(x.A, M_0, M_1)$ gives the desired equation. $\square$

To prove that the function type supports the Kan operations is equally straightforward. Like the reduction rules for function application, the reduction rules for coe and hcom in the function type (Figure 3.2) are stable under interval substitution. Therefore, it is only necessary to check that the reduced terms are well-typed and satisfy the necessary equations (e.g., that coercion and composition $r \to r$ are identity functions); the results for the unreduced terms then follow by coherent head expansion. We leave these verifications as an exercise for the reader.

### 3.1.6.2 V types

The univalence axiom is realized in cubical type theory by V types, which create lines of types from isomorphisms. Although we will not have much need to work with V types directly—we mostly use the univalence theorem they imply—they do provide a more thorough exercise of the lemmas defined above: unlike function types, the operational semantics rules of V types are not stable under interval substitution.

Given $\Psi \Vdash A, B$ type and an isomorphism $\Psi \Vdash I \in A \simeq B$ between them, the V type $\Psi, x:\mathbb{I} \Vdash V_x(A, B, I)$ type is a path that connects the types $A$ and $B$: we will have $\Psi \Vdash V_0(A, B, I) = A$ type and $\Psi \Vdash V_1(A, B, I) = B$ type, as the reduction rules in Figure 3.1 suggest. While we will not go through this in any detail here, coercion along a V type applies the isomorphism: $\lambda a.\text{coe}_{x.V_x(A,B,I)}^{0\to 1}(a)$ is equal, up to a path, to the underlying