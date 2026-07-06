1.2. GRAY OPERATIONS

**Theorem 1.2.4.1** (Steiner, Ara-Maltsiniotis). *There is a unique colimit preserving monoidal structure on $(0, \omega)$-cat, up to a unique monoidal isomorphism, making the functor $\nu_{|\mathrm{ADC}_{\mathrm{B}}}: \mathrm{ADC}_{\mathrm{B}} \to (0, \omega)$-cat a monoidal functor, when $\mathrm{ADC}_{\mathrm{B}}$ is endowed with the monoidal structure given by the Gray tensor product.*

*Proof.* This is [AM20, theorem A.15].

**Definition 1.2.4.2.** The monoidal product on $(0, \omega)$-cat induced by the previous theorem is called the *Gray tensor product* and is denoted by $\otimes$. It's unit is $\mathbf{D}_0$. If $C$ and $D$ are $(0, \omega)$-categories with an atomic and loop free basis, we have by construction

$$C \otimes D := \nu(\lambda C \otimes \lambda D).$$

**Proposition 1.2.4.3.** *There are equivalences*

$$(C \otimes D)^{\mathrm{op}} \cong D^{\mathrm{op}} \otimes C^{\mathrm{op}} \qquad (C \otimes D)^{\circ} \cong C^{\circ} \otimes D^{\circ} \qquad (C \otimes D)^{\mathrm{co}} \cong D^{\mathrm{co}} \otimes C^{\mathrm{co}}$$

*natural in $C, D : (0, \omega)$-cat.*

*Proof.* This is [AM20, proposition A.20].

**Definition 1.2.4.4.** The functors

$$\_ \otimes [1] : (0, \omega)\text{-cat} \to (0, \omega)\text{-cat} \quad [1] \otimes \_ : (0, \omega)\text{-cat} \to (0, \omega)\text{-cat}$$

are respectively called the *Gray cylinder* and the *Gray $\circ$-cylinder*.

**Proposition 1.2.4.5.** *Let $C$ be an $(\infty, \omega)$-category. The following canonical square*

$$\begin{array}{c} C \otimes \{0, 1\} \longrightarrow C \otimes [1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ 1 \coprod 1 \longrightarrow [C, 1] \end{array}$$

*is cocartesian*

*Proof.* As all these functors commute with colimits, it is sufficient to demonstrate this assertion when $C$ is a globular sum, and *a fortiori* when $C$ admits a loop free and atomic basis. In this case, remark that all the morphisms appearing in canonical cartesian square

$$\begin{array}{c} \lambda C \otimes \{0, 1\} \longrightarrow \lambda C \otimes [1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ 1 \coprod 1 \longrightarrow [\lambda C, 1] \end{array}$$

are quasi-rigid. The results then follow from an application of theorem 1.2.1.26.

**Remark 1.2.4.6.** Applying the duality $(\_)^{\mathrm{op}}$ to the computation achieved in appendix B.1 of [AM20], we can give an explicit expression of $\mathbf{D}_n \otimes [1]$. As a polygraph, the generating arrows of $\mathbf{D}_n \otimes [1]$ are:

$$\begin{array}{l} e_k^{\epsilon} \otimes \{0\} \quad e_k^{\epsilon} \otimes \{1\} \quad e_k^{\epsilon} \otimes [1] \\ a_0^- \otimes e_k^{\epsilon} \qquad a_0^+ \otimes e_k^{\epsilon} \qquad a \otimes e_k^{\epsilon} \end{array}$$

47