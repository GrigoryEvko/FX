A logic of programs 27

Functions

$$\overline{(a : A) \rightarrow B \text{ val}} \quad \overline{\lambda a. N \text{ val}} \quad \frac{F \longmapsto F'}{F M \longmapsto F' M} \quad \overline{(\lambda a. N) M \longmapsto N[M/a]}$$

Products

$$\overline{(a : A) \times B \text{ val}} \quad \overline{\langle M, N \rangle \text{ val}} \quad \frac{P \longmapsto P'}{\text{fst}(P) \longmapsto \text{fst}(P')} \quad \frac{P \longmapsto P'}{\text{snd}(P) \longmapsto \text{snd}(P')}$$
$$\overline{\text{fst}(\langle M, N \rangle) \longmapsto M} \quad \overline{\text{snd}(\langle M, N \rangle) \longmapsto N}$$

Natural numbers

$$\overline{\text{Nat val}} \quad \overline{\text{zero val}} \quad \overline{\text{suc}(M) \text{ val}}$$

$$\frac{N \longmapsto N'}{\text{elim}_{\text{Nat}}(n.B; N; Z, n.b.S) \longmapsto \text{elim}_{\text{Nat}}(n.B; N'; Z, n.b.S)}$$

$$\overline{\text{elim}_{\text{Nat}}(n.B; \text{zero}; Z, n.b.S) \longmapsto Z}$$

$$\overline{\text{elim}_{\text{Nat}}(n.B; \text{suc}(N); Z, n.b.S) \longmapsto S[N/n, \text{elim}_{\text{Nat}}(n.B; N; Z, n.b.S)/b]}$$

Identity types

$$\overline{\text{Id}(A, M_0, M_1) \text{ val}} \quad \overline{\text{refl}(M) \text{ val}}$$

$$\frac{P \longmapsto P'}{\text{elim}_{\text{Id}}(a_0.a_1.p.B, P, a.N) \longmapsto \text{elim}_{\text{Id}}(a_0.a_1.p.B, P', a.N)}$$

$$\overline{\text{elim}_{\text{Id}}(a_0.a_1.p.B, \text{refl}(M), a.N) \longmapsto N[M/a]}$$

$$\begin{array}{cccccc} \text{Unit} & & & \text{Void} & & \text{Universe} \\ \overline{\text{Unit val}} & \overline{\star \text{ val}} & & \overline{\text{Void val}} & & \overline{\text{U val}} \end{array}$$

Figure 2.2: Operational semantics for a bare-bones type theory