Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:45

for \(\top\)-slice fully faithful multipliers is inverse to \((\widehat{\mathbf{a}}_{\forall u}^{j[u]}, \widehat{\mathbf{a}}_{\mathrm{reid}x_u}^{\mathrm{app}_u})\) and therefore denotes an inverse of application: variable capture. Furthermore, regarding the context of \(c_{\forall}\), we remark that for \(\top\)-slice fully faithful multipliers there is an isomorphism of contexts

\[
\begin{array}{l} (\Delta , \widehat {\mathbf {a}} _ {\forall u} ^ {j [ u ]}, y: B, \widehat {\mathbf {a}} _ {\forall [ u ]} ^ {\forall u}) \cong_ {3. 4} \left(\Delta , \widehat {\mathbf {a}} _ {\forall u} ^ {j [ u ]}, \widehat {\mathbf {a}} _ {\forall [ u ]} ^ {\forall u}, \forall u \mid y: B \left[ \widehat {\mathbf {a}} _ {\forall u} ^ {j [ u ]}, \widehat {\mathbf {a}} _ {\text {reid} x _ {u}} ^ {\text {app} _ {u}} \right]\right) \\ \cong_ {6. 3 1} \left(\Delta , \forall u \mid y: B, \widehat {\mathbf {a}} _ {\forall u} ^ {j [ u ]}\right) \tag {10.1} \\ \end{array}
\]

so, recalling from Section 7.1.3 that \(i:\mathbb{I}\) translates to \(\widehat{\mathbf{a}}_{\forall i}^{j[i]}\) in the internal context, there really is a close correspondence to what happens in the BCM system.

We remark that if \(\mathbb{U}\) is \(\top\)-slice fully faithful but not necessarily shard-free, then the \(\Phi\)-rule remains valid for creating terms of a transpension type \(C = \langle \langle [u] \mid D \rangle\). Indeed, using pole Theorem 9.1 we can then define:

\[
\Phi_ {u} \text {   pole   } c _ {\forall} := \text { mod } _ {\langle [ u ]} (\text { unmer } _ {u} \cdot_ {\forall u} c _ {\forall}): \langle \langle [ u ] \mid D \rangle .
\]

The non-trivial computation rule follows from the \(\eta\)-rule for projections (Proposition 3.3) and quantification Theorem 6.31.

Theorem 10.1. If \(\mathbb{U}\) is \(\top\)-slice fully faithful and shard-free, then the \(\Phi\)-rule (Fig. 10) is sound and indeed derivable from TRANSP:ELIM for all \(C\).

Proof. Use the case-eliminator for  \( \langle\langle[u]\mid Unit\rangle \)  (Theorem 9.3):

\[
\Phi_ {u} c _ {\partial} c _ {\forall} := \text { case } (\text { mod } _ {\langle [ u ]} \text { unit }) \text { of } \left\{\text { pole } \mapsto c _ {\partial} \mid \text { mer } _ {-} \mapsto c _ {\forall} \right\}.
\]

□

10.3. The \(\Psi\)-type. BCM's \(\Psi\)-combinator (Fig. 11, also known as Gel [CH21]) constructs a line \(\forall (i:\mathbb{I}).\mathsf{U}\) in the universe with endpoints \(A_{\epsilon}\) from a relation \(R:A_0\to A_1\to \mathsf{U}\). A section of the \(\Psi\)-type with endpoints \(a_{\epsilon}\) is a proof of \(Ra_0a_1\). The constructor in \(\Psi\) creates a section \(\forall (i:\mathbb{I}).\Psi_iA_0A_1(x_0.x_1.R)\) from the expected inputs. The disappearance of \(\Theta\) in the premises of \(\Psi\) and in \(\Psi\) is entirely analogous to the shape application rule FF:FORALL:ELIM in Fig. 1. The eliminator out \(\Psi\) extracts from a section of the \(\Psi\)-type the proof that its endpoints satisfy the relation \(R\).

In fact, using the typing rules of FFTraS and a strictness axiom as in Section 8.3 we can already implement a stronger  \( \Psi \) -type, also given in Fig. 11, where  \( \Theta \)  does not disappear but gets universally quantified. This is done by strictifying the right hand sides below: \( ^{22} \)

\[
\alpha : \Psi_ {i} A _ {0} A _ {1} (x _ {0}. x _ {1}. R) := (\hat {x} _ {0}: (\operatorname{refl}: i \equiv_ {\mathbb {I}} 0) \rightarrow A _ {0}) \times (\hat {x} _ {1}: (\operatorname{refl}: i \equiv_ {\mathbb {I}} 1) \rightarrow A _ {1}) \times
\]

\[
\langle [ i ] (R [ (\lambda i. \hat {x} _ {0}) 0 \operatorname{refl} / x _ {0}, (\lambda i. \hat {x} _ {1}) 1 \operatorname{refl} / x _ {1} ])
\]

\[
\operatorname{in} \Psi_ {i} a _ {0} a _ {1} r := \alpha^ {- 1} (\lambda \operatorname{refl}. a _ {0}, \lambda \operatorname{refl}. a _ {1}, \operatorname{mer} [ i ] r)
\]

\[
\operatorname{out} \Psi (i. q) := \operatorname{unmer} (i. \pi_ {3} (\alpha (q)))
\]

The fact that this construction is isomorphic to \( A_{\epsilon} \) at endpoint \( \epsilon \) follows from our findings about poles in Section 2.2.

When we move to MTraS, once again we translate the context \((\Delta, u : \mathbb{U}, \Theta)\) to \((\Delta, \widehat{\mathbf{a}}_{\forall u}^{j[u]}, \Theta)\), which we treat as a single abstract context \(\Gamma\). By a reasoning identical to that in Eq. (10.1), applying \(\widehat{\mathbf{a}}_{\forall u}^{j[u]}\) only affects the non-fresh part \(\Theta\) if the shape \(\mathbb{U}\) is \(\top\)-slice fully faithful. This leads to the MTraS rules listed in Fig. 11. Note again how substitutions

\( ^{22} \) For the identity type, we use pattern-matching abstractions to abbreviate the usage of the J-rule. We are in an extensional type system anyway.