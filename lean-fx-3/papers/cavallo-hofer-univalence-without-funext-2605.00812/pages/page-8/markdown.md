CAVALLO, HÖFER

**Proposition 3.7 (cf. [50, §4.2])** Given $A \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\Gamma)$, $B \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\Gamma.A)$, we have a dependent sum $\Sigma_A B \in \mathrm{Ty}(\Gamma)$ given by

$$\Gamma_S \vdash (\Sigma_A B)_S := \sum_{a:A_S} B_S(a), \qquad \Gamma_S, \langle a_S, b_S \rangle: (\Sigma_A B)_S \vdash (\Sigma_A B)_P := A_P(a_S) + B_P(a_S, b_S).$$

**Proposition 3.8 (cf. [50, §4.4])** Given $A \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\Gamma)$ and $u, v \in \mathrm{Tm}(\Gamma, A)$, we have an identity type $u =_A v \in \mathrm{Ty}(\Gamma)$ given by

$$\Gamma_S \vdash (u =_A v)_S := (u_S =_{A_S} v_S), \qquad \Gamma_S, p: (u =_A v)_S \vdash (u =_A v)_P := 0,$$

with, for $u \in \mathrm{Tm}(\Gamma, A)$, the reflexive path $\mathsf{refl}_u \in \mathrm{Tm}(\Gamma, u =_A u)$ given by

$$\Gamma_S \vdash (\mathsf{refl}_u)_S := \mathsf{refl}_{u_S}: (u_S =_{A_S} u_S), \qquad \Gamma_S.0 \vdash (\mathsf{refl}_u)_P := \mathsf{elim}_0: \Gamma_P.$$

**Proof.** For every $u \in \mathrm{Tm}(\Gamma, A)$, $B \in \mathrm{Ty}(\Gamma.A.u = \mathfrak{q})$, $w \in \mathrm{Tm}(\Gamma, B[u, \mathsf{refl}_u])$, $v \in \mathrm{Tm}(\Gamma, A)$, and $p \in \mathrm{Tm}(\Gamma, u =_A v)$, the eliminator $\mathsf{elim}_=^{B,u}(w, v, p) \in \mathrm{Tm}(\Gamma, B[v, p])$ is given by

$$\Gamma_S \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \vdash \mathsf{elim}_=^{B,u}(w, v, p)_S := \mathsf{elim}_=^{B_S, u_S}(w_S, v_S, p_S): B_S[v_S, p_S],$$

$$\Gamma_S, b: B_P[v_S, p_S, \mathsf{elim}_=^{B,u}(w, v, p)_S] \vdash \mathsf{elim}_=^{B,u}(w, v, p)_P := w_P(p_*b): \Gamma_P,$$

where $\Gamma_S.B_P[u_S, \mathsf{refl}_{u_S}, w_S] \vdash w_P: \Gamma_P$ and $p_*: B_P[v_S, p_S, \mathsf{elim}_=^{B,u}(w, v, p)_S] \to B_P[u_S, \mathsf{refl}_{u_S}, w_S]$ is defined by path induction on $p_S$. The $\beta$ rule for $\mathsf{elim}_=$ follows from the same $\beta$ rule in the base model.

**Remark 3.9** Von Glehn takes $(u =_A v)_P$ to be the constant family $A_P(u_S) + A_P(v_S)$. We follow Kovács [30] by instead taking the constant family 0, which simplifies our arguments. Since both definitions satisfy the rules of the identity type, they are equivalent—though not categorically equivalent. The equivalence suffices to imply that our main result Theorem 4.17 transfers to Von Glehn's identity types. This kind of flexibility is common to type formers without strict $\eta$ laws in the polynomial model.

We treat the construction of $\Pi$ types in more detail. Here, we depend crucially on extensivity of coproducts. First, we define families over $A_0 + A_1$ that are inhabited over exactly one of the inclusions.

**Definition 3.10** For types $A_0, A_1$, define the families $A_0 + A_1 \vdash \mathsf{is}_0 := [1, 0]$ and $A_0 + A_1 \vdash \mathsf{is}_1 := [0, 1]$.

**Lemma 3.11** For types $A_0, A_1$, the families $A_0 + A_1 \vdash \mathsf{is}_0, \mathsf{is}_1$ are strict propositions.

**Proof.** More generally, if $A_i \vdash P_i$ are strict propositions for $i \in \{0, 1\}$ then so is $[P_0, P_1]$: we have $u: A_0 + A_1, v_0, v_1: [P_0, P_1] \vdash v_0 \stackrel{=}{=} v_1$ directly from the strict $\eta$ rule since $P_0, P_1) \stackrel{=}{=} P_i(u_i)$.

**Proposition 3.12 (cf. [50, §4.3])** Given $A \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\Gamma)$, $B \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\Gamma.A)$, we have a dependent product $\Pi_A B \in \mathrm{Ty}(\Gamma)$ given by

$$\Gamma_S \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \vdash (\Pi_A B)_S := \sum_{f_S: \prod_{a:A_S} B_S(a)} \prod_{a:A_S} B_P(a, f_S(a)) \to 1 + A_P(a),$$

$$\Gamma_S, \langle f_{SS}, f_{SP} \rangle: (\Pi_A B)_S \vdash (\Pi_A B)_P := \sum_{\substack{a:A_S \\ b:B_P(a, f_{SS}(a))}} \mathsf{is}_0(f_{SP}(a, b)).$$

For $f \in \mathrm{Tm}(\Gamma, \Pi_A B)$ we write $f_{SS}$ and $f_{SP}$ for the first and second component of $f_S$ respectively.

**Proof.** It suffices to define a natural isomorphism $\lambda: \mathrm{Tm}(\Gamma.A, B) \cong \mathrm{Tm}(\Gamma, \Pi_A B) : \mathsf{app}$. By Definition 3.5, an element of $\mathrm{Tm}(\Gamma.A, B)$ corresponds to a pair

$$\Gamma_S \vdash b_S: \prod_{a:A_S} B_S(a), \qquad \Gamma_S \vdash b_P: \prod_{a:A_S} B_P(a, b_S(a)) \longrightarrow \Gamma_P + A_P(a).$$

8