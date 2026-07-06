CAVALLO, HÖFER

By Definition 3.5 and the curry-uncurry isomorphism, an element of \(\mathrm{Tm}(\Gamma, \Pi_A B)\) corresponds to a triple

\[
\Gamma_ {S} \vdash f _ {S S} \colon \prod_ {a: A _ {S}} B _ {S} (a), \qquad \qquad \Gamma_ {S} \vdash f _ {S P} \colon \prod_ {a: A _ {S}} B _ {P} \bigl (a, f _ {S S} (a) \bigr) \longrightarrow 1 + A _ {P} (a),
\]

\[
\Gamma_ {S} \vdash f _ {P} \colon \prod_ {a: A _ {S}} \left(\sum_ {b: B _ {P} (a, f _ {S S} (a))} \mathfrak {i s} _ {0} (f _ {S P} (a, b))\right) \longrightarrow \Gamma_ {P}.
\]

Now, note that we have for all types \(X, Y, Z\) that

\[
\sum_ {f: X \to 1 + Y} \prod_ {x: X} Z ^ {\mathfrak {i s} _ {0} (f x)} \stackrel {{\triangle}} {{=}} \prod_ {x: X} \sum_ {u: 1 + Y} Z ^ {\mathfrak {i s} _ {0} (u)} \stackrel {{\triangle}} {{=}} \prod_ {x: X} \left(\sum_ {\star : 1} Z ^ {\mathfrak {i s} _ {0} (\mathfrak {i n} _ {0} (\star))} + \sum_ {y: Y} Z ^ {\mathfrak {i s} _ {0} (\mathfrak {i n} _ {1} (y))}\right) \stackrel {{\triangle}} {{=}} (Z + Y) ^ {X}.
\]

Applying this strict isomorphism to the above yields the desired bijection.

Proposition 3.13 (cf. [50, §4.2]) We have a nullary coproduct \(0 \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}\) and binary coproduct \(A + B \in \mathrm{Ty}(\Gamma)\) for \(A, B \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\Gamma)\) given by

\[
\Gamma_ {S} \quad \vdash (A + B) _ {S} := A _ {S} + B _ {S}, \quad \Gamma_ {S} \quad \vdash 0 _ {S} := 0,
\]

\[
\Gamma_ {S}. (A _ {S} + B _ {S}) \vdash (A + B) _ {P} := [ A _ {P}, B _ {P} ], \quad \Gamma_ {S}. 0 \vdash 0 _ {P} := \operatorname{elim} _ {0}.
\]

These satisfy the strict \(\eta\) rule and are extensive.

Proposition 3.14 (cf. [32, Proposition 7.1.6]) We have a universe \(\mathcal{U} \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(1)\) with decoding function \(\mathsf{E}\ell \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(1.\mathcal{U})\) (which we usually leave implicit) given by

\[
1 \quad \vdash \mathcal {U} _ {S} := \sum_ {A _ {S}: \mathcal {U}} \mathcal {U} ^ {A _ {S}}, \quad 1, \langle A _ {S}, A _ {P} \rangle : \mathcal {U} _ {S} \quad \vdash \mathsf {E} \ell_ {S} := A _ {S},
\]

\[
1, \langle A _ {S}, A _ {P} \rangle : \mathcal {U} _ {S} \vdash \mathcal {U} _ {P} := 0, \quad 1, \langle A _ {S}, A _ {P} \rangle : \mathcal {U} _ {S}, a _ {S}: \mathsf {E} \ell_ {S} \langle A _ {S}, A _ {P} \rangle \vdash \mathsf {E} \ell_ {P} := A _ {P} (a _ {S}).
\]

### 3.2 A dependent right adjoint

The category \(\mathbb{C}\) is a reflective subcategory of \(\mathbf{Poly}(\mathbb{C})\): the functor \(-_{S}\colon \mathbf{Poly}(\mathbb{C})\to \mathbb{C}\) has a fully faithful right adjoint \(\bigcirc_S\colon \mathbb{C}\to \mathbf{Poly}(\mathbb{C})\) given on objects by \(\bigcirc_S\Gamma := (\Gamma ,0)\). Von Glehn [50] uses this adjunction to define the model that we defined manually above, transferring it from \(\mathbb{C}\). Both functors extend to pseudomorphisms of models in the sense of Kaposi, Huber, and Sattler [28, §4].

Lemma 3.15 The adjunction \(\bigcirc_S\colon \mathbb{C}\leftrightarrows \mathbf{Poly}(\mathbb{C}): -_S\) lifts to an adjunction of pseudomorphisms of models, with left adjoint projecting to shapes of types and terms, and the right adjoint given on types and terms by \(\bigcirc_S A := (A,0)\) and \(\bigcirc_S a := (a,\mathsf{elim}_0)\).

Proof. Immediate from the definition of context extension and that  \( 0 + 0 \cong 0 \) .

The right adjoint morphism induces a dependent right adjoint (cf. [25, §7]).

Corollary 3.16 The operation \(\mathrm{Ty}(\Gamma_S) \to \mathrm{Ty}(\Gamma), A \mapsto (\bigcirc_S A) \eta_\Gamma\) defines a dependent right adjoint.

Proof. \(\mathrm{Tm}(\Gamma, (\bigcirc_S A) \eta_\Gamma) \cong (\mathbf{Poly}(\mathbb{C}) / \bigcirc_S \Gamma)(\Gamma, \bigcirc_S \Gamma_S. \bigcirc_S A) \cong (\mathbb{C} / \Gamma_S)(\Gamma_S, \Gamma_S. A) \cong \mathrm{Tm}(\Gamma_S, A)\).

Henceforth, we denote by \(\bigcirc_S\) the dependent right adjoint, not the morphism. The composite mapping \(A \mapsto \bigcirc_S(A_S)\) defines a pointed endofunctor on \(\mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\Gamma)\) (and a lex operation in the sense of [16, Remark 5]). If clear from context, we write just \(\bigcirc_S A\) for this composite.

9