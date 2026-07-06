Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:25

**Definition 3.4.** Given $A$ type, define isBDisc($A$) type as follows.

$$\text{isBDisc}(A) := (a:A)(b:A) \to \text{islso}(\text{Path}_A(a,b), \text{Bridge}_A(a,b), \text{loosen}_A)$$

As we mentioned in Section 2.4, the type islso is always a proposition [Uni13, Theorem 4.3.2]; any two proofs of islso are connected by a path. A function type with propositional codomain is again a proposition [Uni13, Example 2.6.2], so isBDisc($A$) is a proposition. We define the universe of bridge-discrete types as $\mathcal{U}_{\text{BDisc}} := (A : \mathcal{U}) \times \text{isBDisc}(A)$.

Before continuing, we recall some standard results from univalent type theory. The proofs we reference are conducted using Martin-Löf identity types, but can be readily adapted to cubical path types by way of Lemma 1.3.

**Proposition 3.5.** Let $A$ type and let $a : A, b : A \gg R$ type be a relation on $A$. Suppose we have a family of maps with right inverses:

$$\begin{array}{l} \triangleright F \in (a:A)(b:A) \to R\langle a,b \rangle \to \text{Path}_A(a,b), \\ \triangleright G \in (a:A)(b:A) \to \text{Rinv}(R\langle a,b \rangle, \text{Path}_A(a,b), Fab). \end{array}$$

The Fab is an isomorphism for all $a, b : A$.

Proof. [Rij18, Corollary 1.2.6].

**Proposition 3.6.** Let $A$ type, $a : A \gg B_0, B_1$ type, and $F \in (a:A) \to B_0 \to B_1$ be given. Then $\lambda\langle a,b \rangle.\langle a,Fab \rangle \in ((a:A) \times B_0) \to (a:A) \times B_1$ is an isomorphism if and only if $Fa$ is an isomorphism for all $a : A$.

Proof. [Uni13, Theorem 4.7.7].

**Definition 3.7.** A type is contractible if it is a proposition and inhabited.

**Proposition 3.8.** Any function between contractible types is an isomorphism.

Proof. This is an elementary consequence of the definition.

**Proposition 3.9.** For any $A$ type and $M \in A$, the type $(a : A) \times \text{Path}_A(M,a)$ is contractible.

Proof. [Uni13, Lemma 3.11.8].

Taken together, these results give us a convenient method for showing that a type is bridge-discrete without reference to $\text{loosen}_A$.

**Lemma 3.10.** Suppose we have a family of maps with right inverses:

$$\begin{array}{l} \triangleright F \in (a:A)(b:A) \to \text{Bridge}_A(a,b) \to \text{Path}_A(a,b), \\ \triangleright G \in (a:A)(b:A) \to \text{Rinv}(\text{Bridge}_A(a,b), \text{Path}_A(a,b), Fab). \end{array}$$

Then $A$ is bridge-discrete. In particular, if $\text{Bridge}_A(a,b)$ and $\text{Path}_A(a,b)$ are isomorphic for all $a, b : A$, then $A$ is bridge-discrete.

Proof. By Proposition 3.5, Fab is an isomorphism for all $a, b : A$. By Proposition 3.6, we conclude that $(b : A) \times \text{Bridge}_A(a,b)$ and $(b : A) \times \text{Path}_A(a,b)$ are isomorphic for all $a : A$. The latter is contractible by Proposition 3.9, so the former is contractible as well. Thus $\lambda\langle b,p \rangle.\langle b,\text{loosen}_A(p) \rangle \in ((b:A) \times \text{Path}_A(a,b)) \to (b:A) \times \text{Bridge}_A(a,b)$ is an isomorphism for all $b : A$, so $A$ is bridge-discrete by Proposition 3.6.

**Lemma 3.11.** Let $A$ type and $a : A \gg B$ type be given. If $B$ is bridge-discrete for all $a : A$, then we have the following isomorphism for all $a_0, a_1 : A$, $t : B[a_0/a]$, $t' : B[a_1/a]$, and $p : \text{Path}_A(a_0, a_1)$.

$$\text{Path}_{x.B[p@x/a]}(t,t') \simeq \text{Bridge}_{x.B[\text{loosen}_A(p)@x/a]}(t,t')$$