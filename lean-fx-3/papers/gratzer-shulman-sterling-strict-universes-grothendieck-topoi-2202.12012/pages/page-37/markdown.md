STRICT UNIVERSES FOR GROTHENDIECK TOPOI

37

5.2.3. QUESTION. Can $E$ be chosen in Diagram 37 to make the isomorphism $j_*j^*E \rightarrow j_*O$ an *identity* map?

Although identity of objects is not properly part of the language of category theory, it becomes meaningful when considering *internal categories* as we do in Section 5.2.4 below. We will see that the realignment axiom (U8) for a full internal subtopos corresponds to the ability to construct a version of Diagram 37 in which $j_*j^*E = j^*O$ strictly.

5.2.4. INTERNAL RECOLLEMENT. Let $\mathcal{U}$ be a universe in $\mathcal{X}$ and let $p: E \rightarrow U$ be a generic family for $\mathcal{U}$; then $U$ constitutes a *full internal subtopos* of $\mathcal{X}$ in the sense of Bénabou [Bén73]. Consequently we may think of $\mathcal{U}$ as a topos $C^*U$ in every slice $\mathcal{X}_{/C}$ of $\mathcal{X}$; hence any monomorphism $J \rightarrow C$ in $\mathcal{X}$ corresponds to a subterminal object in $\mathcal{X}_{/C}$, *i.e.* an open subtopos of $C^*U$. Therefore we may replay the global and local recollement for each $C^*U$ using the same constructions.

Letting $J: \Omega$ be a proposition in $\mathcal{X}$, we note that the exponential family $E^J \rightarrow U^J$ is generic for the *open* subtopos of $U$ determined by the proposition $J$. We will write $J_*: U^J \rightarrow U$ for the function that sends a family $O: U^J$ to its dependent product $\prod_{z:J} Oz$; the left adjoint $J^*: U \rightarrow U^J$ takes a type $A$ to the constant family $\lambda_*: J.A$. Likewise we may obtain a generic family for the *closed* subtopos by considering the subobject $U_{\star J} \subseteq U$ spanned by types $A$ such that $p[A] \times J \rightarrow J$ is an isomorphism; following Rijke, Shulman, and Spitters [RSS20], we will refer to such types as $J$-connected.

We may now revisit our Question 5.2.3 concerning Diagram 37 in the internal language. Let $O: U^J$ be an object of the open subtopos and let $K: J_*O \rightarrow U_{\star J}$ be a family of $J$-connected objects. Then an affirmative answer to Question 5.2.3 would produce some $E: U$ together with an isomorphism $f_E: (\sum_{x:J_*O} Kx) \rightarrow E$ in $U$ such that $j^*E = O$ strictly and $j^*f_E$ is strictly equal to $\lambda z: J.\lambda(x,y).xz$. In other words, we are asking for a type constructor Glue on $U$ with the following interface:

$$\text{Glue}: \prod_{J:\Omega} \prod_{O:U^J} \prod_{K:J_*O \rightarrow U_{\star J}} \{G: U \mid \forall z: J.G = Oz\}$$

$$\text{glue}: \prod_{J:\Omega} \prod_{O:U^J} \prod_{K:J_*O \rightarrow U_{\star J}} \{f: (\sum_{x:J_*O} Kx) \cong \text{Glue } O K \mid \forall z: J.\forall x,y.f(x,y) = xz\}$$

It is not difficult to verify that the existence of such a type constructor is equivalent to the internal realignment axiom discussed in Section 5.1.

5.2.5. LEMMA. *Let $G$ be a realignment structure for $U$ in the sense of Definition 5.1.3; then there exists a Glue connective satisfying the described rules.*

PROOF. Let $O, K$ as above and consider the application of $G$ to $B := \sum_{x:J_*O} Kx$ and the partial isomorphism $z: J \vdash B \cong Oz$, which exists because each fiber of $K$ is $J$-connected. From this pair we thus obtain both Glue $JOK$ and glue $JOK$. ■

5.2.6. LEMMA. *Conversely, suppose that we have a Glue connective in the sense described above; then there exists a realignment structure in the sense of Definition 5.1.3.*

PROOF. Given a type $B$ and a partial isomorph $(J, A): \text{Iso}_\mathcal{U}(B)^+$, we let $O := \lambda z: J.\pi_1(Az)$ and $K := \lambda x: J_*O.\{y: B \mid \forall z: J.(\pi_2(Az))(xz) = y\}$. Then we consider the total isomorph given by the pair $(\text{Glue } JOK, \pi_2 \circ (\text{glue } JOK)^{-1})$. ■