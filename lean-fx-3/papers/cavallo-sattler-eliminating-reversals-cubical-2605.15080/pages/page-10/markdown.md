10

Eliminating reversals from cubical type theories

#### 3.3.2 Filling

Cofibrations are used to specify the filling operator. We first introduce the abbreviation \(\Phi_{\mathrm{fill}}\) for the environment

\[
(\mathrm{A}: \mathbb {I} \to \mathrm{Ty}, \mathrm{P}: \mathrm{Cof}, \mathrm{a}: ([ \mathrm{P} ], \mathrm{i}: \mathbb {I}) \to \mathrm{A} (\mathrm{i}), \mathrm{j}: \mathbb {I}, \mathrm{a} _ {0}: \mathrm{A} (\mathrm{j}), [ \mathrm{P} \to \mathrm{a} (\mathrm{j}) \equiv \mathrm{a} _ {0}: \mathrm{A} (\mathrm{j}) ]).
\]

This environment specifies a line ( \( \mathbb{I} \) -indexed family) of types A and a “partial” line of terms a over it, defined whenever some cofibration P is true, together with a fully-defined term  \( a_{0} \)  at some index  \( \mathsf{A}(\mathsf{j}) \)  that coincides with  \( \mathsf{a}(\mathsf{j}) \)  when P holds. Given this input, the filling operator outputs a line  \( (\mathsf{k}:\mathbb{I})\to\mathsf{A}(\mathsf{k}) \)  that “extends” both a and  \( a_{0} \)  in the following sense.

\[
\begin{array}{l} \text { fill } \quad : \quad (\Phi_ {\text { fill }}, k: \mathbb {I}) \Rightarrow A (k) \\ \_ \quad : \quad (\Phi_ {\text {fill}}, k: \mathbb {I}, P) \Rightarrow \operatorname{fill} (A, P, a, j, a _ {0}, k) \equiv a (k): A (k) \\ \_ \quad : \quad (\Phi_ {\text {fill}}) \Rightarrow \operatorname{fill} (A, P, a, j, a _ {0}, j) \equiv a _ {0}: A (j) \\ \end{array}
\]

The special case where \(\mathsf{P} = \bot\) is called coercion by Angiuli et al. [2, §2.7] and converts a term at some index \(\mathsf{a}_0:\mathsf{A}(\mathsf{j})\) to a term at any other index \(\mathsf{A}(\mathsf{k})\).

▶ Notation 19. Over the environment (A : (i : I) → Ty, j : I, a₀ : A(j), k : I), write coe(A, j, a₀, k) := fill(A, ⊥, ⟨i⟩elim⊥ᵀᵐ(A(i)), j, a₀, k) : A(k).
▶ Notation 20. We write  \( \text{fill}^{j\to k}(A,[P_{1}\mapsto a_{1},\ldots,P_{n}\mapsto a_{n}],a_{0}) \)  for  \( \text{fill}(A,P,a,j,a_{0},k) \)  where  \( P=P_{1}\cup\cdots\cup P_{n} \)  (with some choice of parentheses) and a is defined from  \( a_{1},\ldots,a_{n} \)  by cases using  \( \text{elim}_{\cup}^{Tm} \) . We write  \( \text{coe}^{j\to k}(A,a_{0}) \)  for  \( \text{coe}(A,j,a_{0},k) \) .
▶ Remark 21. This definition of fill is a suitable base for strict cubical type theory over arbitrary interval theories. In the presence of certain interval structure, it can be reduced to special cases. For theories with connections,  \( fill^{0\to1} \)  and  \( fill^{1\to0} \)  suffice; see Cavallo, Mörtberg, and Swan [10, Theorem 14 with Lemma 8]. With two connections and a reversal, this can be further reduced to  \( fill^{0\to1} \), as in Cohen et al.'s type theory [12]; see Angiuli et al. [2, §3.4]. We refer to Cavallo, Mörtberg, and Swan [10] for more detailed comparisons.

#### 3.3.3 Paths

A path is an \(\mathbb{I}\)-indexed term taking two fixed values at the endpoints \(0,1:\mathbb{I}\). Path types internalize paths:

\[
\begin{array}{l} \text { Path } \quad : \quad (\mathrm{A}: (\mathrm{i}: \mathbb {I}) \to \mathrm{Ty}, \mathrm{a} _ {0}: \mathrm{A} (0), \mathrm{a} _ {1}: \mathrm{A} (1)) \Rightarrow \mathrm{Ty} \\ \lambda^ {\mathbb {I}} \quad : \quad ([ \mathrm{A}: (\mathrm{i}: \mathbb {I}) \rightarrow \mathrm{Ty} ], \mathrm{a}: (\mathrm{i}: \mathbb {I}) \rightarrow \mathrm{A} (i)) \Rightarrow \operatorname{Path} (\mathrm{A}, \mathrm{a} (0), \mathrm{a} (1)) \\ - \mathbb {Q} -: ([ \mathrm{A}: (\mathrm{i}: \mathbb {I}) \rightarrow \mathrm{Ty}, \mathrm{a} _ {0}: \mathrm{A} (0), \mathrm{a} _ {1}: \mathrm{A} (1) ], \mathrm{p}: \operatorname{Path} (\mathrm{A}, \mathrm{a} _ {0}, \mathrm{a} _ {1}), \mathrm{i}: \mathbb {I}) \Rightarrow \mathrm{A} (\mathrm{i}) \\ \end{array}
\]

The equations for path types state that \(\lambda^{\mathbb{I}}(\mathsf{a})\mathbb{O}\mathsf{i}\equiv \mathsf{a}(\mathsf{i})\) and \(\mathsf{p}\equiv \lambda^{\mathbb{I}}(\langle \mathsf{i}\rangle \mathsf{p}\mathbb{O}\mathsf{i})\), as for function types, as well as that \(\mathsf{p}\mathbb{O}0\equiv \mathsf{a}_0\) and \(\mathsf{p}\mathbb{O}1\equiv \mathsf{a}_1\) for \(\mathsf{p}:\operatorname {Path}(\mathsf{A},\mathsf{a}(0),\mathsf{a}(1))\). See Uemura [37, §4.6.3, Type constructors] for a fully formal presentation.

▶ Notation 22. We write \(\lambda\mathbf{i}.a\) as shorthand for \(\lambda^{\mathbb{I}}\langle\mathbf{i}\rangle a\). We abbreviate “non-dependent” path types \(\text{Path}(\langle\_\rangle A, a_0, a_1)\), where the line of types is constant, as \(a_0 \sim^A a_1\) or simply \(a_0 \sim a_1\).

#### 3.3.4 Glue types

In cubical type theories, univalence is not an axiom but is instead derived from a type former that can construct \(\mathbb{I}\)-indexed types from equivalences. Universes closed under this type