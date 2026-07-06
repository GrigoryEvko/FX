E. Cavallo and C. Sattler

19

satisfying $\mathsf{P} \to \mathsf{a}(j) \equiv \mathsf{a}_0 : \mathsf{A}(j)$, $\mathsf{P}' \to \mathsf{a}'(y) \equiv \mathsf{a}_0' : \mathsf{A}'(y)$, and $\overline{\mathsf{P}} \to \overline{\mathsf{a}}(j, y) \equiv \overline{\mathsf{a}}_0 : \overline{\mathsf{A}}(\mathsf{a}_0, \mathsf{a}_0')$. Abbreviating $\mathsf{a}_+(\mathsf{k}) := F\mathrm{fill}^{\mathrm{j} \to \mathrm{k}}(\mathsf{A}, [\mathsf{P} \mapsto \mathsf{a}], \mathsf{a}_0)$ and $\mathsf{a}_+'(\mathsf{z}) := G\mathrm{fill}^{\mathrm{y} \to \mathrm{z}}(\mathsf{A}', [\mathsf{P}' \mapsto \mathsf{a}'], \mathsf{a}_0')$, we must exhibit a term of type $\overline{\mathsf{A}}(\mathsf{k}, \mathsf{z}, \mathsf{a}_+(\mathsf{k}), \mathsf{a}_+'(\mathsf{z}))$. We take the iterated filling expression

$$
\begin{array}{l}
G\mathrm{fill}^{\mathrm{y} \to \mathrm{z}}(\langle \mathrm{x} \rangle \overline{\mathsf{A}}(\mathrm{k}, \mathrm{x}, \mathrm{a}_+(\mathrm{k}), \mathrm{a}_+'(\mathrm{x})), [\overline{\mathsf{P}} \mapsto \langle \mathrm{x} \rangle \overline{\mathsf{a}}(\mathrm{k}, \mathrm{x})], \\
F\mathrm{fill}^{\mathrm{j} \to \mathrm{k}}(\langle \mathrm{i} \rangle \overline{\mathsf{A}}(\mathrm{i}, \mathrm{y}, \mathrm{a}_+(\mathrm{i}), \mathrm{a}_0'), [\overline{\mathsf{P}} \mapsto \langle \mathrm{i} \rangle \overline{\mathsf{a}}(\mathrm{i}, \mathrm{y})], \overline{\mathsf{a}}_0)).
\end{array}
$$

▶ **Component 54** (S, $\Pi$ types). In the environment consisting of $\mathsf{A} : \mathsf{Ty}$, $\mathsf{A}' : \mathsf{Ty}$, a 1-to-1 correspondence $\overline{\mathsf{A}} : (\mathsf{A}, \mathsf{A}') \to \mathsf{Ty}$, families $\mathsf{B} : \mathsf{A} \to \mathsf{Ty}$, $\mathsf{B}' : \mathsf{A}' \to \mathsf{Ty}$, and 1-to-1 correspondences $\overline{\mathsf{B}} : ([\mathsf{a} : \mathsf{A}, \mathsf{a}' : \mathsf{A}'], \overline{\mathsf{a}} : \overline{\mathsf{A}}(\mathsf{a}, \mathsf{a}'), \mathsf{b} : \mathsf{B}(\mathsf{a}), \mathsf{b}' : \mathsf{B}'(\mathsf{a}')) \to \mathsf{Ty}$, we take the relation sending $\mathsf{f} : F\Pi(\mathsf{A}, \mathsf{B})$ and $\mathsf{f}' : G\Pi(\mathsf{A}', \mathsf{B}')$ to $\Pi\mathsf{a} : \mathsf{A}$. $\Pi\mathsf{a}' : \mathsf{A}'$. $\Pi\overline{\mathsf{a}} : \overline{\mathsf{A}}(\mathsf{a}, \mathsf{a}')$. $\overline{\mathsf{B}}(\overline{\mathsf{a}}, \mathsf{f}(\mathsf{a}), \mathsf{f}'(\mathsf{a}'))$.

For Path types, we exploit the fact that we can convert between non-dependent Path, $F$Path, and $G$Path types, which follows from the fact that both types support coercion.

▶ **Lemma 55.** Over $([\mathsf{C} : \mathsf{Ty}, \mathsf{c}_0 : \mathsf{C}, \mathsf{c}_1 : \mathsf{C}], \mathsf{p} : F\mathrm{Path}(\langle \_\rangle \mathsf{C}, \mathsf{c}_0, \mathsf{c}_1))$, we have a term $\mathrm{decode}^F(\mathsf{p}) : \mathsf{c}_0 \sim^{\mathsf{C}} \mathsf{c}_1$.

**Proof.** We have $F\mathrm{coe} : (\mathsf{A} : (\mathsf{x} : F\mathbb{I}) \to \mathsf{Ty}, \mathsf{y} : F\mathbb{I}, \mathsf{a}_0 : \mathsf{A}(\mathsf{y}), \mathsf{z} : F\mathbb{I}) \Rightarrow \mathsf{A}(\mathsf{z})$, and instantiating with the arguments $(\langle \mathsf{x} \rangle (\mathsf{c}_0 \sim^{\mathsf{C}} \mathsf{p} \otimes_F \mathsf{x}), F0, (\lambda_-, \mathsf{c}_0), F1)$ yields the desired expression.

▶ **Corollary 56.** Over $(\mathsf{C} : F\mathbb{I} \to \mathsf{Ty}, \mathsf{c}_0 : \mathsf{C}(F0))$, $\Sigma\mathsf{c}_1 : \mathsf{C}(F1).F\mathrm{Path}(\mathsf{C}, \mathsf{c}_0, \mathsf{c}_1)$ is contractible.

**Proof.** Applying $F$ to singleton contractibility (Proposition 38), we get over the environment $(\mathsf{C} : F\mathbb{I} \to \mathsf{Ty}, \mathsf{c}_0 : \mathsf{C}(F0))$ a term of type $F\mathrm{isContr}(F\Sigma\mathsf{c}_1 : \mathsf{C}(F1).F\mathrm{Path}(\mathsf{C}, \mathsf{c}_0, \mathsf{c}_1))$. The type formers $F\Sigma$ and $F\Pi$ satisfy the rules for $\Sigma$- and $\Pi$-types, so we can define equivalences $F\Sigma(A, B) \simeq \Sigma(A, B)$ and $F\Pi(A, B) \simeq \Pi(A, B)$. Combined with Lemma 55, we can therefore derive $\mathrm{isContr}(\Sigma\mathsf{c}_1 : \mathsf{C}(F1).F\mathrm{Path}(\mathsf{C}, \mathsf{c}_0, \mathsf{c}_1))$.

Of course, Corollary 56 also holds when we replace $F$ with $G$.

▶ **Component 57** (S, path types). To define SPath, we are given $\mathsf{A} : F\mathbb{I} \to \mathsf{Ty}$ and $\mathsf{A}' : G\mathbb{I} \to \mathsf{Ty}$ with a 1-to-1 correspondence $\overline{\mathsf{A}} : (\mathsf{i} : F\mathbb{I}, \mathsf{x} : G\mathbb{I}, \mathsf{a} : \mathsf{A}(\mathsf{i}), \mathsf{a}' : \mathsf{A}'(\mathsf{x})) \to \mathsf{Ty}$, terms $\mathsf{a}_0 : \mathsf{A}(F0)$ and $\mathsf{a}_0' : \mathsf{A}'(G0)$ with $\overline{\mathsf{a}}_{00} : \overline{\mathsf{A}}(F0, G0, \mathsf{a}_0, \mathsf{a}_0')$, and terms $\mathsf{a}_1 : \mathsf{A}(F1)$ and $\mathsf{a}_1' : \mathsf{A}'(G1)$ with $\overline{\mathsf{a}}_{11} : \overline{\mathsf{A}}(F1, G1, \mathsf{a}_1, \mathsf{a}_1')$.

We need to define a 1-to-1 correspondence between $F\mathrm{Path}(\mathsf{A}, \mathsf{a}_0, \mathsf{a}_1)$ and $G\mathrm{Path}(\mathsf{A}', \mathsf{a}_0', \mathsf{a}_1')$. We take the relation sending $\mathsf{p}$ and $\mathsf{p}'$ to the iterated $\Sigma$-type with components

$$
\begin{array}{l}
\overline{\mathsf{a}}_{10} : \overline{\mathsf{A}}(F1, G0, \mathsf{a}_1, \mathsf{a}_0'). \\
\overline{\mathsf{a}}_{01} : \overline{\mathsf{A}}(F0, G1, \mathsf{a}_0, \mathsf{a}_1'). \\
\overline{\mathsf{a}}_{\bullet 0} : F\mathrm{Path}(\langle \mathsf{i} \rangle \overline{\mathsf{A}}(\mathsf{i}, G0, \mathsf{p} \otimes_F \mathsf{i}, \mathsf{a}_0'), \overline{\mathsf{a}}_{00}, \overline{\mathsf{a}}_{10}). \\
\overline{\mathsf{a}}_{\bullet 1} : F\mathrm{Path}(\langle \mathsf{i} \rangle \overline{\mathsf{A}}(\mathsf{i}, G1, \mathsf{p} \otimes_F \mathsf{i}, \mathsf{a}_1'), \overline{\mathsf{a}}_{01}, \overline{\mathsf{a}}_{11}). \\
\overline{\mathsf{a}}_{0\bullet} : G\mathrm{Path}(\langle \mathsf{x} \rangle \overline{\mathsf{A}}(F0, \mathsf{x}, \mathsf{a}_0, \mathsf{p}' \otimes_G \mathsf{x}), \overline{\mathsf{a}}_{00}, \overline{\mathsf{a}}_{01}). \\
\overline{\mathsf{a}}_{1\bullet} : G\mathrm{Path}(\langle \mathsf{x} \rangle \overline{\mathsf{A}}(F1, \mathsf{x}, \mathsf{a}_1, \mathsf{p}' \otimes_G \mathsf{x}), \overline{\mathsf{a}}_{10}, \overline{\mathsf{a}}_{11}). \\
\overline{\mathsf{a}}_{\bullet\bullet} : F\mathrm{Path}(\langle \mathsf{i} \rangle G\mathrm{Path}(\langle \mathsf{x} \rangle \overline{\mathsf{A}}(\mathsf{i}, \mathsf{x}, \mathsf{p} \otimes_F \mathsf{i}, \mathsf{p}' \otimes_G \mathsf{x}), \overline{\mathsf{a}}_{\bullet 0} \otimes_F \mathsf{i}, \overline{\mathsf{a}}_{\bullet 1} \otimes_F \mathsf{i}), \overline{\mathsf{a}}_{0\bullet}, \overline{\mathsf{a}}_{1\bullet}).
\end{array}
$$

An element consists effectively of a family of witnesses $\overline{\mathsf{a}}_{\bullet\bullet} \otimes_F \mathsf{i} \otimes_G \mathsf{x} : \overline{\mathsf{A}}(\mathsf{i}, \mathsf{x}, \mathsf{p} \otimes_F \mathsf{i}, \mathsf{p}' \otimes_G \mathsf{x})$ satisfying $\overline{\mathsf{a}}_{\bullet\bullet} \otimes_F F0 \otimes_G G0 \equiv \overline{\mathsf{a}}_{00}$ and $\overline{\mathsf{a}}_{\bullet\bullet} \otimes_F F1 \otimes_G G1 \equiv \overline{\mathsf{a}}_{11}$. We define $\mathrm{M}\lambda^{\mathbb{I}}$ and $\otimes_{\mathrm{M}}$ to be abstraction and application of such families.

It remains to check that this relation is a 1-to-1 correspondence. Fix $\mathsf{p} : F\mathrm{Path}(\mathsf{A}, \mathsf{a}_0, \mathsf{a}_1)$ and consider the type of pairs of $\mathsf{p}' : G\mathrm{Path}(\mathsf{A}', \mathsf{a}_0', \mathsf{a}_1')$ with the data (1). Given the preceding