14

Eliminating reversals from cubical type theories

▶ Component 32 (T, filling). We interpret filling by iterated filling, first in one component of the interval variable and then in the other, defining  \( \text{Tfill}(A, P, a, (j_0, j_1), a_0, (k_0, k_1)) \)  to be

\[
\operatorname{fill} ^ {\mathrm{j} _ {1} \rightarrow \mathrm{k} _ {1}} (\langle \mathrm{i} _ {1} \rangle \mathrm{A} (\mathrm{k} _ {0}, \mathrm{i} _ {1}), [ \mathrm{P} \mapsto \langle \mathrm{i} _ {1} \rangle \mathrm{a} (\mathrm{k} _ {0}, \mathrm{i} _ {1}) ], \operatorname{fill} ^ {\mathrm{j} _ {0} \rightarrow \mathrm{k} _ {0}} (\langle \mathrm{i} _ {0} \rangle \mathrm{A} (\mathrm{i} _ {0}, \mathrm{j} _ {1}), [ \mathrm{P} \mapsto \langle \mathrm{i} _ {0} \rangle \mathrm{a} (\mathrm{i} _ {0}, \mathrm{j} _ {1}) ], \mathrm{a} _ {0})).
\]

We interpret type formers that do not involve the interval, namely  \( \Sigma \)  and  \( \Pi \)  types, identity types, and U and El, as themselves. This leaves path types, glue types, and suspensions. We interpret the path type as a type of squares with fixed values at the coordinates  \( T0 = (0, 1) \)  and  \( T1 = (1, 0) \) , encoded as an iterated path type consisting of the two unfixed points at  \( (0, 0) \)  and  \( (1, 1) \) , four 1-dimensional paths forming a boundary, and a 2-dimensional path relating them.

▶ Component 33 (T, path types). We define TPath(A, a01, a10) to be the iterated path type

\[
\begin{array}{l} \Sigma \mathrm{a} _ {0 0}: \mathrm{A} (0, 0). \Sigma \mathrm{a} _ {1 1}: \mathrm{A} (1, 1). \\ \Sigma \mathrm{p} _ {\bullet 0}: \text {Path} (\langle \mathrm{i} _ {0} \rangle \mathrm{A} (\mathrm{i} _ {0}, 0), \mathrm{a} _ {0 0}, \mathrm{a} _ {1 0}). \Sigma \mathrm{p} _ {\bullet 1}: \text {Path} (\langle \mathrm{i} _ {0} \rangle \mathrm{A} (\mathrm{i} _ {0}, 1), \mathrm{a} _ {0 1}, \mathrm{a} _ {1 1}). \\ \Sigma \mathrm{p} _ {0 \bullet}: \text {Path} (\langle \mathrm{i} _ {1} \rangle \mathrm{A} (0, \mathrm{i} _ {1}), \mathrm{a} _ {0 0}, \mathrm{a} _ {0 1}). \Sigma \mathrm{p} _ {1 \bullet}: \text {Path} (\langle \mathrm{i} _ {1} \rangle \mathrm{A} (1, \mathrm{i} _ {1}), \mathrm{a} _ {1 0}, \mathrm{a} _ {1 1}). \\ \operatorname{Path} \left(\left\langle \mathrm{i} _ {0} \right\rangle \operatorname{Path} \left(\left\langle \mathrm{i} _ {1} \right\rangle \mathrm{A} \left(\mathrm{i} _ {0}, \mathrm{i} _ {1}\right), \mathrm{p} _ {\bullet 0} @ \mathrm{i} _ {0}, \mathrm{p} _ {\bullet 1} @ \mathrm{i} _ {0}\right), \mathrm{p} _ {0 \bullet}, \mathrm{p} _ {1 \bullet}\right) \\ \end{array}
\]

and set  \( \mathrm{T}\lambda^{\mathbb{I}}(\mathbf{a}):=(\_,\_,\_,\_,\_,\lambda\mathbf{i}_{0}.\lambda\mathbf{i}_{1}.\mathbf{a}(\mathbf{i}_{0},\mathbf{i}_{1})) \)  and  \( t\otimes_{T}(\mathbf{i}_{0},\mathbf{i}_{1}):=t.6\otimes\mathbf{i}_{0}\otimes\mathbf{i}_{1} \) , where the first five components in  \( T\lambda^{I} \)  are determined by the final one.

We write \(\mathrm{T}\lambda \mathrm{i}_0,\mathrm{i}_1.a\) as shorthand for \(\mathrm{T}\lambda^{\mathbb{I}}(\langle \mathrm{i}_0,\mathrm{i}_1\rangle a)\).

Remark 34. This iterated path type could be naturally expressed as an extension type. Introduced by Riehl and Shulman for simplicial type theory [28, §2.2] and discussed by Angiuli [1, §3.5] in the context of cubical type theory, these are types of \( n \)-cubes with fixed values on some cofibration. In a theory with these types, TPath could be defined as an extension type over the cofibration in two variables \( \mathbf{i}_0: \mathbb{I}, \mathbf{i}_1: \mathbb{I} \vdash (\mathbf{i}_0 \approx 0 \cap \mathbf{i}_1 \approx 1) \cup (\mathbf{i}_0 \approx 1 \cap \mathbf{i}_1 \approx 0) \).

To interpret glue and suspension types, we need to convert between inhabitants of  \( \text{Path}(\mathbb{C}, \mathbb{c}_{0}, \mathbb{c}_{1}) \)  and inhabitants of  \( \text{TPath}(\langle\mathbf{i}_{0}, \mathbf{i}_{1}\rangle\mathbb{C}(\mathbf{i}_{0}), \mathbb{c}_{0}, \mathbb{c}_{1}) \) . First, the easy direction:

▶ Notation 35. Over the environment ( \( [C: I \to Ty, c_{0}: C(0), c_{1}: C(1)], p: Path(C, c_{0}, c_{1}) \) ), we define thicken(p) := Tλi₀, i₁.p @ i₀ : TPath( \( \langle i_{0}, i_{1} \rangle C(i_{0}), c_{0}, c_{1} \) ).

For the inverse, we extract the “anti-diagonal” of a square by inverting it along one axis—a standard construction using the filling operation—and then extracting the diagonal.

▶ Definition 36 (Path inversion). Over the environment ([C : Ty, c₀ c₁ : C], p : c₀ ∼ᶜ c₁), we define sym(p) := λi.fill¹→⁰(⟨_)C, [i ≈ 0 ↦ ⟨_)c₁, i ≈ 1 ↦ ⟨j⟩p @ j], c₁) : c₁ ∼ᶜ c₀.

▶ Definition 37. Over ([C : I → Ty, c₀ : C(0), c₁ : C(1)], q : TPath(⟨i₀, i₁⟩C(i₀), c₀, c₁)), we define anti(q) := λi.sym(⟨j⟩q @T (i, j)) @ i : Path(C, c₀, c₁).

To show that these constitute an equivalence, we use the contractibility of dependent singleton types:

▶ Proposition 38. Over the environment (C : I → Ty, c₀ : C(0)), we have a term of type isContr(Σc₁:C(1).Path(C, c₀, c₁)).

Proof (cf. [1, §3.2]). For the center of contraction, take the pair  \( s_{0} := (\_, \lambda i.\text{coe}^{0 \to i}(C, c_{0})) \)  (whose first component is determined by its second). Given a singleton s, we have a path  \( \lambda j.(\_, \lambda i.\text{fill}^{0 \to i}(C, [j \approx 0 \mapsto \langle k \rangle s_{0} @ k, j \approx 1 \mapsto \langle k \rangle s @ k], c_{0})) \)  from  \( s_{0} \)  to s.