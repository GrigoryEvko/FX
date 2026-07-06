CAVALLO, HÖFER

The $\beta$ rules state that $\Gamma, a_i: A_i, \Delta(\mathsf{in}_i(a_i)) \vdash \mathsf{elim}_+^P(a_0.u_0, a_1.u_1, \mathsf{in}_i(a_i)) \stackrel{*}{=} a_i$. The $\eta$ rule states, as shown below, that we can test strict equality of terms depending on $A_0 + A_1$ by checking equality on constructors.

$$\frac{\Gamma, u: A_0 + A_1, \Delta \vdash t(u), t'(u): P(u)}{\text{for } i \in \{0, 1\}: \Gamma, a: A_i, \Delta(\mathsf{in}_i(a)) \vdash t(\mathsf{in}_i(a)) \stackrel{*}{=} t'(\mathsf{in}_i(a)) : P(\mathsf{in}_i(a))} \\ \hline \Gamma, u: A_0 + A_1, \Delta \vdash t(u) \stackrel{*}{=} t'(u): P(u)$$

The elimination rule and $\eta$ law for 0 are similar.

$$\frac{\Gamma, v: 0, \Delta(v) \vdash P(v)}{\Gamma, v: 0, \Delta(v) \vdash \mathsf{elim}_0^P(v): P(v)} \qquad \qquad \frac{\Gamma, v: 0, \Delta(v) \vdash t(v), t'(v): P(v)}{\Gamma, v: 0, \Delta(v) \vdash t(v) \stackrel{*}{=} t'(v): P(v)}$$

Semantically, the above rules mean that the split fibration $\mathbf{Ty}_{\mathbb{C}}$ has split fibred coproducts [27, Definition 1.8.1]: each $\mathbf{Ty}_{\mathbb{C}}(\Gamma)$ has chosen finite coproducts and the substitution functors $\mathbf{Ty}(\Gamma) \to \mathbf{Ty}(\Delta)$ preserve them strictly. For inference rules, see for example Von Glehn [50, §2.3.5] or Angiuli and Gratzer [5, §2.5.1 and §2.5.3].

**Remark 3.4** Strict $\eta$ laws for coproducts are often omitted from the syntax of type theory due to issues with strict equality checking. In the simply-typed $\lambda$-calculus, strict equality checking for coproducts with the $\eta$ law is decidable but difficult. Ghani [22] addresses the case of binary coproducts; Scherer [37] handles the empty type. In ITT, the $\eta$ law for the empty type makes strict equality undecidable: with this law, deciding whether $a: A \vdash \mathsf{in}_0(\star) \stackrel{*}{=} \mathsf{in}_1(\star): 1 + 1$ requires deciding whether $A$ implies 0. To our knowledge, it is an open problem whether strict equality is decidable for ITT with binary coproducts and their $\eta$ law; see, for example, discussion between Shulman, Kovács, and others on Proof Assistants StackExchange [40].

We further require that our coproducts are *extensive*. The syntactic counterpart is often called *large elimination*. This means that given types $\Gamma, a_i: A_i, \Delta(\mathsf{in}_i(a_i)) \vdash P_i(a_i)$ for $i \in \{0, 1\}$, there is a type $\Gamma, u: A_0 + A_1, \Delta(u) \vdash P_0, P_1$ satisfying $\Gamma, a_i: A_i, \Delta(\mathsf{in}_i(a_i)) \vdash P_0, P_1) \stackrel{*}{=} P_i(a_i)$. Using the strict $\eta$ rule, for every family $\Gamma.A_0 + A_1 \vdash P$ there is a canonical strict isomorphism $P \cong [P\mathsf{in}_0, P\mathsf{in}_1]$. Furthermore, for all such $P$ there is a strict isomorphism $\sum_{u:A+B} P(u) \cong \sum_{a:A} P(\mathsf{in}_0(a)) + \sum_{b:B} P(\mathsf{in}_1(b))$. This is used in particular in the construction of dependent product types (Proposition 3.12).

For the rest of this section, we assume $\mathbb{C}$ has extensive finite coproducts of types with the strict $\eta$ rule.

**Definition 3.5** The presheaf of terms $\mathrm{Tm}_{\mathbf{Poly}(\mathbb{C})}: (\int \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})})^{\mathrm{op}} \to \mathbf{Set}$ is given by $\mathrm{Tm}_{\mathbf{Poly}(\mathbb{C})}(\Gamma, A) := \sum_{a_S: \mathrm{Tm}(\Gamma_S, A_S)} \mathbf{Ty}(\Gamma_S)(A_P[a_S], \Gamma_P)$. We refer to the components again as *shapes* and *positions*.

**Proposition 3.6** ($\mathbf{Poly}(\mathbb{C}), \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}, \mathrm{Tm}_{\mathbf{Poly}(\mathbb{C})}$) *extends to a category with families by setting*

$$(\Gamma.A)_S := \Gamma_S.A_S, \qquad (\Gamma.A)_P := \Gamma_P \mathsf{p}_{A_S} + A_P, \qquad (\mathsf{p}_A)_S := \mathsf{p}_{A_S}, \qquad (\mathsf{p}_A)_P := \mathsf{in}_0: \Gamma_P \to \Gamma_P \mathsf{p} + A_P,$$

$$(\mathsf{q}_A)_S := \mathsf{q}_{A_S}, \qquad (\mathsf{q}_A)_P := \mathsf{in}_1: A_P \to \Gamma_P \mathsf{p} + A_P, \qquad \langle \sigma, a \rangle_S := \langle \sigma_S, a_S \rangle, \qquad \langle \sigma, a \rangle_P := [\sigma_P, a_P].$$

**Proof.** Given $\sigma: \Delta \to \Gamma$ and $a \in \mathrm{Tm}(\Delta, A\sigma)$ we have $\langle \sigma, a \rangle_S: \Delta_S \to \Gamma_S.A_S$ and $\langle \sigma, a \rangle_P: \Gamma_P \sigma_S + A_P \langle \sigma_S, a_S \rangle \to \Delta_P$ in $\mathbf{Ty}(\Delta)$. Clearly, all desired equations hold on shapes since they hold in $\mathbb{C}$. We have $(\mathsf{p}\langle \sigma, a \rangle)_P = [\sigma_P, a_P] \circ \mathsf{in}_0 \mathsf{p} = \sigma_P$ and $(\mathsf{q}\langle \sigma, a \rangle)_P = [\sigma_P, a_P] \circ \mathsf{in}_1 \mathsf{p} = a_P$. This shows $\mathsf{p}\langle \sigma, a \rangle = \sigma$ and $\mathsf{q}\langle \sigma, a \rangle = a$. Furthermore, $\langle \mathsf{p}, \mathsf{q} \rangle_P = [\mathsf{p}_P, \mathsf{q}_P] = [\mathsf{in}_0, \mathsf{in}_1] = \mathrm{id}$ and $(\langle \sigma, a \rangle \tau)_P = \tau_P \circ [\sigma_P, a_P] \tau_S = [\tau_P \circ \sigma_P \tau_S, \tau_P \circ a_P \tau_S] = \langle \sigma \tau, a \tau \rangle_P$. This shows $\langle \mathsf{p}, \mathsf{q} \rangle = \mathrm{id}$ and $\langle \sigma, a \rangle \tau = \langle \sigma \tau, a \tau \rangle$. $\square$

### 3.1 Type formers

We give the interpretations in $\mathbf{Poly}(\mathbb{C})$ of $\Sigma$, identity, $\Pi$, binary and nullary coproduct, and universe types.

7