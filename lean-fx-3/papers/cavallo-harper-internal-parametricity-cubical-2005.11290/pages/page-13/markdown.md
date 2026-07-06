Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:13

Coercion and composition are together referred to as the Kan operations, being inspired by the Kan condition of algebraic topology [Kan55]. For each type we wish to introduce to cubical type theory, we must explain how the Kan operations evaluate at that type. This can be carried out for all the standard type formers of Martin-Löf type theory (functions, products, inductive types, universes); we refer to Angiuli [Ang19] for a thorough accounting of those results.

Using coercion, we can prove the converse to Lemma 1.1: if two functions take equal arguments to equal results, then they are equal as functions.

Lemma 1.2. Let $x : \mathbb{I} \gg A$ type, $x : \mathbb{I}, a : A \gg B$ type, $F_0 \in ((a:A) \to B)[0/x]$, and $F_1 \in ((a:A) \to B)[1/x]$ be given. Then we have the following.

$$\frac{H \in (a_0 : A[0/x]) (a_1 : A[1/x]) (p : \mathsf{Path}_{x.A}(a_0, a_1)) \to \mathsf{Path}_{x.B[p \otimes x/a]} (F_0 a_0, F_1 a_1)}{\mathsf{funext}(H) \in \mathsf{Path}_{x.(a:A) \to B}(F_0, F_1)}$$

Proof. $\mathsf{funext}(H) := \lambda^\mathbb{I}x.\lambda a.H(\mathsf{coe}_{x.A}^{x \to 0}(a))(\mathsf{coe}_{x.A}^{x \to 1}(a))(\lambda^\mathbb{I}y.\mathsf{coe}_{x.A}^{x \to y}(a))$.

Essentially, given an interval variable $x : \mathbb{I}$ and an element $a$ of $A$ (at index $x$), we can extend the point $a$ to a path over $x.A$ by coercion.

Coercion and composition also give us an analogue of the Martin-Löf identity type elimination principle (often called “J”) for paths.

Lemma 1.3. Let $A$ type and $M \in A$ be given. Suppose we are given the following:

$\triangleright a : A, p : \mathsf{Path}_A(M, a) \gg C$ type,

$\triangleright N \in C[M, \lambda^\mathbb{I}...M/a, p]$,

$\triangleright M' \in A$ and $P \in \mathsf{Path}_A(M, M')$.

Then there is some $\mathsf{J}_{a.p.C}(N, P) \in C[M', P/a, p]$.

Proof. Define an auxiliary $x : \mathbb{I}, y : \mathbb{I} \gg Q \in A$ as follows.

$$Q := \mathsf{hcom}_A^{0 \to y} (P \otimes 0; x = 0 \hookrightarrow ...P \otimes 0, x = 1 \hookrightarrow y.P \otimes y)$$

Set $\mathsf{J}_{a.p.C}(N, P) := \mathsf{coe}_{x.C[Q[1/y], \lambda^\mathbb{I}y.Q/a, p]}^{0 \to 1}(N)$.

This is slightly weaker than the elimination principle enjoyed by Martin-Löf’s elimination principle, as it is not the case that $\mathsf{J}_{a.p.C}(N, \lambda^\mathbb{I}...M) = N \in C[M, \lambda^\mathbb{I}...M/a, p]$ in general; this equation may be shown to hold up to a path, but does not hold up to exact equality. One may separately introduce identity types to cubical type theory that do satisfy this principle, either via a special construction [CCHM15, ABC$^+$19] or as particular indexed inductive types [CH19a], and in this case one has $\mathsf{Id}_A(M, M') \simeq \mathsf{Path}_A(M, M')$. By univalence, this isomorphism implies that path and identity types satisfy the same theorems; in particular, it justifies our citing theorems about identity types in homotopy type theory as theorems about path types going forward. Of course, these theorems are often more easily proven in cubical type theory by reasoning directly with paths.

1.4. V-types and univalence. The Kan operations account for one direction of the univalence axiom: the mapping from paths between types to isomorphisms. The inverse is defined using V-types, which produce paths in the universe from isomorphisms.$^1$

First, let us take the opportunity to define isomorphism precisely.

$^1$Some formulations of cubical type theory instead use Glue-types, which have V-types as a special case. The points we make here about V-types apply equally well to Glue-types.