26

Martin-Löf's type theory

An essential property of the open judgments is their stability under substitution: if some open judgment $\Gamma \gg \mathcal{J}$ holds and we have a substitution $\Gamma' \gg \gamma \in \Gamma$, then $\Gamma' \gg \mathcal{J}\gamma$ also holds.

# **Rules 2.1.19 (Stability under substitution).**

$$\frac{\Gamma' \gg \gamma = \gamma' \in \Gamma \quad \Gamma \gg A = A' \text{ type}}{\Gamma' \gg A\gamma = A'\gamma' \text{ type}} \quad \frac{\Gamma' \gg \gamma = \gamma' \in \Gamma \quad \Gamma \gg M = M' \in A}{\Gamma' \gg M\gamma = M'\gamma' \in A\gamma}$$

$$\frac{\Gamma' \gg \gamma = \gamma' \in \Gamma \quad \Gamma \gg \delta = \delta' \in \Delta}{\Gamma' \gg \delta\gamma = \delta'\gamma' \in \Delta}$$

In particular, we can see the structural rules as arising from this principle. For any $\Gamma$ ctx, we have a trivial identity substitution $\Gamma \gg \text{id}_\Gamma \in \Gamma$ that replaces each variable with itself. Weakening for types and terms then follows from the fact that we also have $\Gamma, b : B \gg \text{id}_\Gamma \in \Gamma$. Similarly, cut follows from the existence of the extended substitutions $\Gamma \gg (\text{id}_\Gamma, N/b) = (\text{id}_\Gamma, N'/b) \in (\Gamma, b : B)$ for any $\Gamma \gg N = N' \in B$. Finally, note that the stability of substitutions themselves under substitution gives us composition of substitutions.

### 2.1.4 Constructing a type system

Now that we have seen how to obtain a type theory from an operational semantics and type system, let us instantiate the framework with an example or two. We list the defining operational semantics rules for a bare-bones language in Figure 2.2, the terms of which are drawn from the following grammar.

$$\begin{array}{l} A, B, M, N, P \quad ::= \quad a \mid (a : A) \rightarrow B \mid \lambda a. N \mid N M \\ \quad \mid (a : A) \times B \mid \langle M, N \rangle \mid \text{fst}(P) \mid \text{snd}(P) \\ \quad \mid \text{Nat} \mid \text{zero} \mid \text{suc}(M) \mid \text{elim}_{\text{Nat}}(n.B; M; N, n.b.P) \\ \quad \mid \text{Id}(A, M, N) \mid \text{refl}(M) \mid \text{elim}_{\text{Id}}(a_0.a_1.p.B, P, a.N) \\ \quad \mid \text{Unit} \mid \star \\ \quad \mid \text{Void} \mid \text{abort} \\ \quad \mid U \end{array}$$

To define a value type system closed under the various type formers, we use the Knaster-Tarski fixed-point theorem [Tar55; DP02, §8.20], which states that any monotone operator on a complete lattice has a least fixed-point. (Here, we only need the theorem for lattices of subsets.)