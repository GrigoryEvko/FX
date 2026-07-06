CAVALLO, HÖFER

Proof. By Lemma 4.14 and $\mathsf{CUA}_{\mathcal{U}}^{\bullet}$ with Lemma 2.10.

Lemma 4.16 A type of $\mathbf{Poly}(\mathbb{C})$ is a proposition exactly if its image under $-_S$ is: naturally in $\Gamma \in \mathbf{Poly}(\mathbb{C})$, given $A \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\Gamma)$ there is a logical equivalence $\mathrm{Tm}_{\mathbb{C}}(\Gamma_S, \mathsf{is}\text{-prop}(A_S)) \longleftrightarrow \mathrm{Tm}_{\mathbf{Poly}(\mathbb{C})}(\Gamma, \mathsf{is}\text{-prop}(A))$.

Proof. By Proposition 3.8, we have that identity types are in the image of $\bigcirc_S$ and preserved by $-_S$. Thus, $\mathrm{Tm}(\Gamma.A.A, \mathsf{qp} =_A \mathsf{q}) \cong \mathrm{Tm}(\Gamma_S.A_S.A_S, (\mathsf{qp} =_A \mathsf{q})_S) \cong \mathrm{Tm}(\Gamma_S.A_S.A_S, \mathsf{qp} =_{A_S} \mathsf{q})$.

Theorem 4.17 If $\mathbb{C} \models \mathsf{CUA}_{\mathcal{U}}^{\bullet}$, then $\mathbf{Poly}(\mathbb{C}) \models \mathsf{CUA}_{\mathcal{U}}^{\bullet}$.

Proof. By Lemma 2.10, it suffices to show $I: \mathcal{U}, A: \mathsf{Fam}(I) \vdash \sum_{B: \mathsf{Fam}(I)} \mathsf{Iso}(I, A, B)$ is contractible. It is inhabited by the identity, so it is enough to show it is a proposition. By Lemma 4.16, it suffices to show $I: \mathcal{U}_S, A: \mathsf{Fam}(I)_S \vdash \sum_{B: \mathsf{Fam}_S(I)} \mathsf{Iso}_S(I, A, B)$ is a proposition in $\mathbb{C}$, and this is Lemma 4.15.

Remark 4.18 Von Glehn [50, §5.1] observes that the outputs of $\mathbf{Poly}(-)$ are also suitable inputs to $\mathbf{Poly}(-)$, meaning the construction can be iterated. Theorem 4.17 implies that iterated polynomial models also inherit $\mathsf{CUA}_{\mathcal{U}}^{\bullet}$ from the base model, though we do not know if there is any use for these models.

## 5 Familial categorical univalence without function extensionality

Using the results from Section 4 together with Von Glehn's counterexample to function extensionality in $\mathbf{Poly}(\mathbb{C})$, which we recall in Section 5.1, we can derive the independence of $\mathsf{FE}_{\mathcal{U}}$ from $\mathsf{ITT} + \mathsf{CCUA}_{\mathcal{U}}$.

### 5.1 Failure of function extensionality in the polynomial model

Von Glehn's proof that $\mathsf{FE}$ fails in $\mathbf{Poly}(\mathbb{C})$ [50, Proposition 4.11] uses the following types:

Definition 5.1 Given $\Gamma \in \mathbf{Poly}(\mathbb{C})$ and $A \in \mathrm{Ty}_{\mathbb{C}}(\Gamma_S)$, define $\top\langle A\rangle \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\Gamma)$ by $\Gamma_S \vdash \top\langle A\rangle_S := 1$ and $\Gamma_S.\top\langle A\rangle_S \vdash \top\langle A\rangle_P := A$.

Proposition 5.2 There exist $f_0, f_1 \in \mathrm{Tm}(1, \top\langle 1 + 1\rangle \to \top\langle 1\rangle)$ with $(f_0 = f_1) \to 0$.

Proof. For each $k \in \{0,1\}$, we define $b_k \in \mathrm{Tm}(1.\top\langle 1 + 1\rangle, \top\langle 1\rangle)$ by setting $1.1 \vdash (b_k)_S := \star: 1$ and $1.1.1 \vdash (b_k)_P := \mathsf{in}_k(\star): 1 + 1$. Take $f_k := \lambda(b_k)$. Unfolding the construction of $\lambda$ in Proposition 3.12, we have $(f_k)_S \doteq \langle (b_k)_S, (b_k)_P \rangle$, so $(f_0 = f_1)_S$ implies $(b_0)_P = (b_1)_P$ and is thus empty.

Proposition 5.3 ([50, Proposition 4.11]) $\mathbf{Poly}(\mathbb{C}) \models \neg \mathsf{FE}_{\mathcal{U}}$.

Proof. The functions from Proposition 5.2 are homotopic since the codomain is a proposition by Lemma 4.16. Note that $\top\langle A\rangle$ belongs to the universe of $\mathbf{Poly}(\mathbb{C})$ for $A: \mathcal{U}$.

### 5.2 Independence of function extensionality from familial categorical univalence

Proposition 5.4 There is a model $\mathbb{C}$ of $\mathsf{ITT}$ with extensive finite coproducts satisfying the strict $\eta$ rule such that $\mathbb{C} \models \mathsf{FE}$ and $\mathbb{C} \models \mathsf{UA}_{\mathcal{U}}$.

Proof. Take the model of $\mathsf{ITT} + \mathsf{FE} + \mathsf{UA}_{\mathcal{U}}$ constructed by Cohen, Coquand, Huber, and Mörtberg [15], whose category of contexts is the category of presheaves on the De Morgan cube category and whose types are dependent cubical sets equipped with a uniform Kan filling operation. Orton and Pitts [34, Theorem 5.14] show that binary coproducts of types can be modeled by coproducts of dependent cubical sets, and it is easy to check the same for nullary coproducts. Thus these coproducts satisfy the strict $\eta$ law and, since every topos is an extensive category [12, Remark 4.10], are also extensive.

Remark 5.5 The particular choice of cubical model is not important in the proof above; any model in the style of Orton and Pitts [34] or Angiuli et al. [4] will do, as will Voevodsky's (non-constructive) simplicial model [29]. There are, however, models of $\mathsf{ITT} + \mathsf{UA}_{\mathcal{U}}$ that do not support extensive finite coproducts of types; see for example the need for a factorization in Shulman [39, Proposition 6.2].

13