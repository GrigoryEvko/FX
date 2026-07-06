Programming in a cubical type theory 71

**Rules 3.1.47 (V type reduction).**

$$\frac{\Psi \Vdash r \in \mathbb{I} \quad \Psi, r \equiv 0 \gg I \in A \simeq B}{\Psi, r \equiv 0 \gg M \in A \quad \Psi \Vdash N \in B \quad \Psi, r \equiv 0 \gg (\text{fst}(I)) M = N \in B}$$
$$\frac{\Psi \Vdash \text{vproj}_r(\text{v}_r(M, N), I) = N \in B}{\Psi \Vdash M \in A \quad \Psi \Vdash I \in A \simeq B}$$

$$\frac{\Psi \Vdash \text{vproj}_0(M, I) = (\text{fst}(I)) M \in A}{\Psi \Vdash \text{vproj}_1(M, N) = N \in B}$$

*Proof.* Again, the reduction rules in the 0 and 1 cases follow immediately by coherent head expansion. We also apply coherent head expansion for the first rule, but now we have to do some case analysis. Let $\Psi' \Vdash \psi \in \Psi$ be given. Then we are in one of three cases.

- Case: $r\psi = 0$. Then $\text{vproj}_r(\text{v}_r(M, N), I)\psi \longmapsto \text{vproj}_r(M, I)\psi$. By the reduction rule for 0 just proven and the assumed equation $\Psi, r \equiv 0 \gg (\text{fst}(I)) M = N \in B$, the latter is equal to $N\psi$ in $B\psi$.
- Case: $r\psi = 1$. Then $\text{vproj}_r(\text{v}_r(M, N), I)\psi \longmapsto \text{vproj}_r(N, I)\psi$, and the latter is equal to $N\psi$ in $B\psi$ by the reduction rule for 1 just proven.
- Case: $r\psi = x$. Then $\text{vproj}_r(\text{v}_r(M, N)\psi, I) \longmapsto N\psi$, and the latter is well-typed by hypothesis. $\square$

With these rules, we have seen enough to get a sense of how proofs of rules proceed in cubical computational type theory. Although the definition of $\mathbb{U}$ is hairy, the process is fairly intuitive filtered through the lens of our battery of lemmas: when we check that a term is well-typed, we need to make sure that its substitution instances behave in a way that is coherent up to the equality of the type.

## 3.2 Programming in a cubical type theory

We now give a few basic definitions and constructions *within* a cubical type theory. These are largely chosen for their relevance to more novel results in *parametric* cubical type theory that we construct in Part III, Chapter 10 and Part IV, Chapter 15, but we hope to also give a taste of cubical argumentation. The reader interested in developing further intuition can find further examples of cubical programming and theorem-proving in [VMA19, §2; Ben19; MP20; ACMZ21]; we also suggest experimenting with the **redtt** proof assistant [redtt] and the **Agda** proof assistant's cubical mode and library [Agda; CubAg].