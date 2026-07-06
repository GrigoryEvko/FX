5:20

E. CAVALLO AND R. HARPER

Vol. 17:4

“$\eta$-principle for extent” that can be proven up to path equality using extent itself, much as dependent elimination for inductive types gives such weak $\eta$-principles.

**Proposition 2.2.** Let $x : \mathbb{I} \gg A$ type, $x : \mathbb{I}, a : A \gg B$ type, $F_0 \in ((a:A) \to B)[\mathbf{0}/\mathbf{x}]$, and $F_1 \in ((a:A) \to B)[\mathbf{1}/\mathbf{x}]$ be given. Then we have the following.

$$\mathsf{Bridge}_{\mathbf{x},(a:A) \to B}(F_0, F_1)$$

$$\simeq$$

$$(a_0: A[\mathbf{0}/\mathbf{x}]) (a_1: A[\mathbf{1}/\mathbf{x}]) (p: \mathsf{Bridge}_{\mathbf{x},A}(a_0, a_1)) \to \mathsf{Bridge}_{\mathbf{x},B[p \otimes \mathbf{x}/a]}(F_0 a_0, F_1 a_1)$$

We can also show that the function extensionality principle induces a corresponding principle for bridges in isomorphism types. We leave the proof to the reader; one can prove it using extent directly, but it also follows formally from Proposition 2.2 and the correspondence between bridges over path types and paths over bridge types.

**Proposition 2.3.** Let $x : \mathbb{I} \gg A, B$ type, $I_0 \in (A \simeq B)[\mathbf{0}/\mathbf{x}]$, and $I_1 \in (A \simeq B)[\mathbf{1}/\mathbf{x}]$ be given. Then we have the following.

$$\frac{H \in (a_0: A[\mathbf{0}/\mathbf{x}]) (a_1: A[\mathbf{1}/\mathbf{x}]) \to \mathsf{Bridge}_{\mathbf{x},A}(a_0, a_1) \simeq \mathsf{Bridge}_{\mathbf{x},B}(\mathsf{fst}(I_0)(a_0), \mathsf{fst}(I_1)(a_1))}{\mathsf{bridge-isoext}(H) \in \mathsf{Bridge}_{\mathbf{x},A \simeq B}(I_0, I_1)}$$

**2.4. Gel-types and relativity.** Finally, we come to the equivalent of univalence in parametric type theory, which we call *relativity*: the correspondence between bridges of types and relations. One direction of the correspondence is given by **Bridge**-types: given a bridge of types $\mathbf{x} : \mathbf{I} \gg A$ type, we have a relation $\mathsf{Bridge}_{\mathbf{x},A}(-,-)$ on $A[\mathbf{0}/\mathbf{x}]$ and $A[\mathbf{1}/\mathbf{x}]$ (which we henceforth simply write as $\mathsf{Bridge}_{\mathbf{x},A}$). As with V-types for univalence, the inverse will be effected by introducing a new type constructor, which we call the **Gel-type**. These resemble the G-types of the BCH model, but apply to relations rather than isomorphisms, hence the name.

We provide rules for **Gel**-types in Figure 6. Unlike the V-type, the **Gel**-type directly converts relations to bridges of types: for any relation $a_0 : A_0, a_1 : A_1 \gg R \in \mathcal{U}$, we have $\lambda^{\mathbf{I}}\mathbf{x}.\mathsf{Gel}_{\mathbf{x}}(A_0, A_1, a_0.a_1.R) \in \mathsf{Bridge}_{\mathcal{U}}(A_0, A_1)$. The introduction rule turns a witness for the relation $\Gamma \gg P \in R[M_0, M_1/a_0, a_1]$ into a bridge $\lambda^{\mathbf{I}}\mathbf{x}.\mathsf{gel}_{\mathbf{x}}(M_0, M_1, P) \in \mathsf{Bridge}_{\mathbf{x},\mathsf{Gel}_{\mathbf{x}}(A_0, A_1, a_0.a_1.R)}(M_0, M_1)$ over the corresponding **Gel**-type, while the elimination rule conversely turns such a bridge into a witness. When we have a relation in the form $R \in A_0 \times A_1 \to \mathcal{U}$, we will abbreviate $\mathsf{Gel}_{\mathbf{r}}(A_0, A_1, a_0.a_1.R\langle a_0, a_1 \rangle)$ as $\mathsf{Gel}_{\mathbf{r}}(A_0, A_1, R)$.

The problem of shifting dimensions in V-types, described in Section 1.4, is no longer an issue when we have affine interval variables; we can express degeneracy in $\mathbf{r}$ using the context restriction $-\backslash \mathbf{r}$. This is fortunate, as the trick for deriving univalence from V-types would not apply here. For univalence, we rely on the fact that the constant path $\lambda^{\mathbb{I}}_\bullet B$ corresponds to the identity isomorphism on $B$; thus we can transform isomorphisms $A \simeq B$ into paths by composing with $\lambda^{\mathbb{I}}_\bullet B$ in a V-type. On the other hand, the constant bridge $\lambda^{\mathbf{I}}_\bullet A$ does *not* necessarily correspond to the identity relation (i.e., the path relation $\mathsf{Path}_B$); rather, it corresponds to the bridge relation $\mathsf{Bridge}_B$. In particular, $\lambda^{\mathbf{I}}_\bullet \mathcal{U}$ will correspond to $\lambda\langle A, B\rangle.(A \times B \to \mathcal{U})$, not $\lambda\langle A, B\rangle.(A \simeq B)$. Thus, a V-like type would only give us bridges for those relations that factor through the bridge relation on one endpoint—more generally, through some bridge $\mathbf{x}, B$ we already have in hand.

We only mean in the above to give some intuition for the difference between the affine and structural situation, not for example to prove beyond a shadow of a doubt that no