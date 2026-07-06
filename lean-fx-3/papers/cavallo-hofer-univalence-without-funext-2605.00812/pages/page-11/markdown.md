CAVALLO, HÖFER

**Lemma 4.5 (In $\mathbb{C}$)** For all $f: \mathcal{U}_J^I(A, B)$, the type is-tot($f$) is a homotopy proposition.

**Proof.** $\Pi_C P$ is a strict proposition if $P$ is: for $p, q: \Pi_C P$ we have $p \doteq \lambda x.p(x) \doteq \lambda y.q(y) \doteq q$. Hence, it follows from Lemma 3.11 that is-tot($f$) is even a strict proposition. $\square$

**Lemma 4.6 (In $\mathbb{C}$)** For all types $I$ and $I \vdash J, B$, the map $(\prod_{i:I} B(i)) \to \prod_{i:I} \sum_{u:J(i)+B(i)} \mathfrak{is}_1(u)$ given by $f \mapsto \lambda i.(\mathfrak{in}_1(f_i u), \star)$ is an equivalence.

**Proof.** $\Pi$ type formation sends families of strict isomorphisms to strict isomorphisms. For $i: I$ we have

$$B(i) \stackrel{\circ}{\cong} \left( \sum_{j:J(i)} 0 \right) + \left( \sum_{b:B(i)} 1 \right) \stackrel{\circ}{\cong} \left( \sum_{j:J(i)} \mathfrak{is}_1(\mathfrak{in}_0(j)) \right) + \left( \sum_{b:B(i)} \mathfrak{is}_1(\mathfrak{in}_1(b)) \right) \stackrel{\circ}{\cong} \sum_{u:J(i)+B(i)} \mathfrak{is}_1(u).$$

In each step we use that to check the commutation out of a coproduct, it suffices to check after precomposing with both inclusions. $\square$

**Corollary 4.7 (In $\mathbb{C}$)** For all types $I$ and $J, A, B: I \to \mathcal{U}$, the map $\mathcal{U}^I(A, B) \to \mathcal{U}_{J,\mathrm{tot}}^I(A, B)$ given by $f \mapsto (\mathfrak{in}_1 \circ f, \lambda i.\lambda a.\star)$ is an equivalence.

**Proof.** Instantiate Lemma 4.6 with index type $\sum_{i:I} A$ and the families $(i, a): \sum_I A \vdash J(i), B(i)$. The result follows by composing with the strict curry-uncurry isomorphism. $\square$

**Lemma 4.8 (In $\mathbb{C}$)** Given a pair of morphisms $f: \mathcal{U}_J^I(B, C)$, $g: \mathcal{U}_J^I(A, B)$, if $f \circ g$ is total then so is $g$.

**Proof.** A morphism $h: \mathcal{U}_J^I(A, B)$ is total if and only if $\prod_{i:I,a:A(i)} \mathfrak{is}_0(h_i a) \to 0$. For $i: I, a: A(i)$ we have $\mathfrak{is}_0(g_i a) \to \mathfrak{is}_0((f \circ g)_i(a))$ by the definition of $\circ$, and so if $f \circ g$ is total we get $\mathfrak{is}_0(g_i a) \to 0$. $\square$

**Corollary 4.9 (In $\mathbb{C}$)** All isomorphism in $\mathcal{U}_J^I$ are total.

**Proof.** By induction, totality transfers along paths. Hence, the claim follows since id is total. $\square$

**Proposition 4.10 (In $\mathbb{C}$)** For all types $I: \mathcal{U}$ and families $J, A, B: \mathcal{U}^I$ we have $(A \cong_{\mathcal{U}^I} B) \simeq (A \cong_{\mathcal{U}_J^I} B)$.

**Proof.** We have a chain of maps $u: \mathcal{U}^I(A, B) \to \mathcal{U}_{J,\mathrm{tot}}^I(A, B) \to \mathcal{U}_J^I(A, B)$. The map $u$ strictly preserves identities and composition and therefore lifts to subtypes of isomorphisms (recall that being an isomorphism is a proposition by Corollary 2.7) via $v: (A \cong_{\mathcal{U}^I} B) \to (A \cong_{\mathcal{U}_J^I} B)$, $\langle f, s, S, r, R \rangle \mapsto \langle uf, us, \mathsf{ap}_u S, ur, \mathsf{ap}_u R \rangle$. Our goal is to show that this restriction is an equivalence. The fibers of $u$ (and thus also $v$) are propositions, since the first component of $u$ is an equivalence by Corollary 4.7 and the second component is an embedding by Lemma 4.5. Hence, $\mathsf{ap}_u: (f =_{\mathcal{U}^I(A,B)} g) \to (uf =_{\mathcal{U}_J^I(A,B)} ug)$ is an equivalence for all $f, g: \mathcal{U}^I(A, B)$. The fibers of $u$ are inhabited over isomorphisms and their sections and retractions by Corollary 4.9 and the fact that sections and retractions of isomorphisms are isomorphisms. Thus, the fibers of $v$ are inhabited. $\square$

### 4.2 Familial categorical univalence

To verify that $\mathbf{Poly}(\mathbb{C})$ inherits $\mathsf{CUA}_{\mathcal{U}}^{\bullet}$, we analyze the wild category $\mathcal{U}^I$ in this model. In $\mathbf{Poly}(\mathbb{C})$, we have for $I: \mathcal{U}$ the type $\mathcal{U}^I$ of $I$-indexed families. Over $A, B: \mathcal{U}^I$, we have the type $A \cong_{\mathcal{U}^I} B$ of isomorphisms between them. We analyze the shapes of these types (i.e. the image under $-_S$) in the base model $\mathbb{C}$. For clarity, we use different notation: define $I: \mathcal{U} \vdash \mathsf{Fam}(I) := \mathcal{U}^I$ and $I: \mathcal{U}, A, B: \mathsf{Fam}(I) \vdash \mathsf{Iso}(I, A, B) := (A \cong_{\mathcal{U}^I} B)$. Now $\mathcal{U}_S$ is a closed type of $\mathbb{C}$, $\mathsf{Fam}_S$ is a family of types over it, $\mathsf{Iso}_S$ is a family over $\mathcal{U}_S$ and two copies of $\mathsf{Fam}_S$, and $\mathsf{Iso}_P$ is a family over $\mathsf{Iso}_S$.

**Remark 4.11** Note that the following data is more ordered than it might seem at first. (1) is exactly the data of an isomorphism in the wild category $\mathcal{U}^{I_S}$. (2) is the data of an isomorphism in the wild category $\mathcal{U}_K^J$ for some $J, K$, modulo the first equivalence. Viewing the morphisms in this wild category again as partial functions, the data given by (3) are exactly the inputs on which the functions are not defined.

11