Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

We may use Lemma 2.13 so that it suffices to check that this property holds when restricted to b-annotated elements of $C^{\mathbb{I}} \times_C E$. Accordingly, we may fix $A :_{\flat} \mathbb{I} \to C$ along with an element $a_0 :_{\flat} A 0$. By Axiom 7, we may assume that $A = \eta \circ A'$ and $a_0 = \eta(a'_0)$ for some unique $A' :_{\flat} \mathbb{I} \to \text{Cat}$ and $a'_0 :_{\flat} A$.

Since $\text{Cat}_{\bullet} \to \text{Cat}$ is cocartesian, we lift $A', a'_0$ to a cocartesian morphism $a' :_{\flat} (i : \mathbb{I}) \to A' i$ with $p' : a' 0 = a'_0$. We now argue that $a = \eta \circ a' : (i : \mathbb{I}) \to \widehat{\mathbb{Q}} A i$ and the induced equality $p : a 0 = a_0$ is the desired universal lift over $A, a$.

After appropriately massaging the input data, it suffices to show that if we are given $H :_{\flat} \Delta^2 \to \square \text{Cat}$ and a lift of this map $h :_{\flat} (t : \Delta_0^2) \to \widehat{\square} H(t)$. There are a handful of paths relating these two $a$ and $A$, but after induction we may definitionally identify (1) $H(0, -)$ with $A$ (2) $h(0, -)$ with $a$. We must show that $h$ extends uniquely to some $\hat{h} : (t : \Delta^2) \to \widehat{\square} H(t)$. By Axiom 7, we may once more factor $H$ and $h$ through Cat whereby the result is an immediate consequence of our construction of $a'$ as a cocartesian lift. □

Corollary 5.13. Cat is a category.

## 6 Full straightening-unstraightening

In this section, we prove the Lurie's straightening-unstraightening theorem which states that for a category $C :_{\flat} \mathcal{U}$, the type $C \to \text{Cat}$ is equivalent to the subcategory of $\text{Cat}_{/C}$ (that is, $\sum_{f: \text{Cat}^{\mathbb{I}}} f(1) = C$) restricted such that its 0- and 1-cells are given cocartesian families and cocartesian functors. Accordingly, for the remainder of this section let us fix $C :_{\flat} \mathcal{U}$ a category.

To do this, we will construct a map $U : (C \to \text{Cat}) \to \text{Cat}_{/C}$ and prove that it is (1) an embedding such that (2) its image on b-annotated elements $C \to \text{Cat}$, and $\mathbb{I} \to (C \to \text{Cat})$ satisfies precisely the above criteria. From this, we show that $(C \to \text{Cat}) \to \text{Cat}_{/C}$ satisfies the expected universal property for the subcategory $\text{Cocart}(C)$ of cocartesian families over $C$ (Corollary 6.6).

Remark 6.1. The material in this section closely follows Cisinski et al. [6] with only minor alterations to make it more convenient in $\text{TT}_{\square}$. In particular, it is from there that we learned of this method of constructing the unstraightening functor and characterizing its image. That such an adaptation is possible is expected but encouraging: the axiomatic approach given by op. cit. is intended to give high-level arguments which can be translated into formal systems satisfying their axioms and our construction of Cat ensures that $\text{TT}_{\square}$ satisfies all the relevant axioms for this argument.

Remark 6.2. We avoid explicitly constructing $\text{Cocart}(C)$ merely to avoid the detour of describing the construction of non-full subcategories. Such constructions are possible using e.g., $(-)_{\mathbb{I}}$.

### 6.1 The unstraightening map

We begin by constructing a map $U$ from $C \to \text{Cat}$ to $\text{Cat}_{/C}$. We break this process into several steps. We begin by considering two particular cocartesian families over $C \to \text{Cat}$:

$$E(f) = \sum_{c:C} f(c) \quad B(f) = C$$

These are both cocartesian families over $C$ and the canonical projection is a cocartesian map $\pi_0 : E \to {}^{cc} B$ as well—and therefore a cocartesian functor. We may therefore glue these together to form a cocartesian family: $\text{Gl}(E, B, \pi_0) : (\text{Cat}^C) \times \mathbb{I} \to \text{Cat}$. First,

let us compute $\text{Gl}(E, B, \pi_0)(-, 1)$ and observe that it is canonically identified to $\lambda_- C$, via the following family of paths:

$$\Phi = \lambda f. \text{ua}(\pi_1) : \prod_{f:C \to \text{Cat}} \text{Gl}(E, B, \pi_0)(f, 1) = C$$

By transposing and using this identification, we obtain:

$$U : (C \to \text{Cat}) \to \text{Cat}_{/C}$$

$$U = \lambda f. (\text{Gl}(E, B, \pi_0)(f, -), \Phi(f))$$

### 6.2 The image of the unstraightening map

Our next task to identify the image of $U$ and, in particular, to show that it is precisely the category of cocartesian families over $C$ and cocartesian functors between them. We therefore compute fibers of $\langle \flat \mid \text{Cat}^C \rangle \to \langle \flat \mid \text{Cat}_{/C} \rangle$ and $\langle \flat \mid \mathbb{I} \to \text{Cat}^C \rangle \to \langle \flat \mid \mathbb{I} \to \text{Cat}_{/C} \rangle$.

In particular, we will show that the fiber over $p :_{\flat} \text{Cat}_{/C}$ is precisely the proposition stating whether $p$ is cocartesian and over $f :_{\flat} \mathbb{I} \to \text{Cat}_{/C}$ it corresponds to the triple of propositions requiring $f(0)$ and $f(1)$ to be cocartesian and $f$ itself to induce a map of cocartesian families. In light of the Segal condition, this characterizes the fibers over arbitrary simplices and, via Axiom 6 and the simpliciality of Cat, proves that $U$ is an embedding. Moreover, our description of the fibers shows that the resultant subcategory of $\text{Cat}_{/C}$ is precisely as described at the beginning of this section.

Lemma 6.3. The fiber of $U$ over $p :_{\flat} \text{Cat}_{/C}$ is a proposition inhabited iff $p$ is cocartesian.

PROOF. Post-composing with directed univalence, we may identify a fiber of $U$ with a fiber of the map:

$$U' : \langle \flat \mid C \to \text{Cat} \rangle \to \langle \flat \mid \sum_{E: \text{Cat}} E \to C \rangle$$

Consider a category $E :_{\flat} \text{Cat}$ and a function $\pi_E :_{\flat} E \to C$. Our goal is to compute the fiber $\sum_{f: \langle \flat | C \to \text{Cat} \rangle} U'(f) = \text{mod}_{\flat}(E, \pi_E)$.

Unfolding $U'$, an element $f :_{\flat} C \to \text{Cat}$ is sent to $(E, \pi_E)$ if and only if we have an equivalence $e :_{\flat} E \simeq \sum_{c:C} f(c)$ and an equation $p :_{\flat} \pi_E = \pi_1 \circ e$. By another application of univalence, this is equivalent to requiring that $\langle \flat \mid \pi_E^{-1}(-) = f \rangle$, so the fiber amounts to $\sum_{f:_{\flat} C \to \text{Cat}} \langle \flat \mid \pi_E^{-1} = f \rangle$. This is a proposition by Proposition 2.8 and by Theorem 4.3 inhabited iff $\pi_E$ is a cocartesian family. □

Lemma 6.4. The fiber of $U$ over $f :_{\flat} \mathbb{I} \to \text{Cat}_{/C}$ is a proposition inhabited iff $f$ is a cocartesian functor between cocartesian families.

PROOF. Rearranging equations, we may identify $\langle \flat \mid \mathbb{I} \to \text{Cat}_{/C} \rangle$ with $\langle \flat \mid \sum_{h: \Delta^2 \to \text{Cat}} h(\bar{2}) = C \rangle$ which we may then identify via directed univalence with $\langle \flat \mid \sum_{E, F: \text{Cat}} E \to F \times F \to C \rangle$. Post-composing $U$ with these maps, we instead consider the following:

$$U' : \langle \flat \mid \mathbb{I} \to \text{Cat}^C \rangle \to \langle \flat \mid \sum_{E, F: \text{Cat}} E \to F \times F \to C \rangle$$

Consider categories $E, F :_{\flat} \text{Cat}$ and functions $\pi_F :_{\flat} F \to C$ and $\alpha :_{\flat} E \to F$. Our goal is to compute the fiber of $U'$ over this data.

Unfolding, an element $h :_{\flat} \mathbb{I} \to \text{Cat}^C$ is sent to $E, F, \pi_F$ if and only if we have the following:

- an equivalence $e_0 :_{\flat} E \simeq \sum_{c:C} h(0, c)$,
- an equivalence $e_1 :_{\flat} F \simeq \sum_{c:C} h(1, c)$,
- a path $\phi :_{\flat} e_1 \circ \alpha = \beta \circ e_0$ where $\beta = \lambda c$. $(-, c)_!$ is given by the cocartesian transport of $h$
- a path $\phi :_{\flat} \pi_F = \pi_0 \circ e_1$.