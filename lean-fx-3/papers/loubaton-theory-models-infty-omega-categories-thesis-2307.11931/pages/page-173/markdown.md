3.4. THE CASE $A := \mathrm{tPsh}(\Delta)^n$

Proof. Let $K$ be a stratified simplicial set, $n$ an integer. By construction, we have two cartesian squares

$$\begin{array}{c} \coprod_{\epsilon \in \{0,1\}} \mathrm{Hom}_{\Delta}([n], \{\epsilon\}) \times \mathrm{Hom}_{\mathrm{tPsh}(\Delta)}(K, \mathrm{N}C) \longrightarrow \mathrm{Hom}_{\Delta}([n], [1]) \times \mathrm{Hom}_{\mathrm{tPsh}(\Delta)}(K, \mathrm{N}C) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{\epsilon \in \{0,1\}} \mathrm{Hom}_{\Delta}([n], \{\epsilon\}) \longrightarrow \mathrm{Hom}_{\mathrm{tSeg}(\mathrm{tPsh}(\Delta))}([K, n], [\mathrm{N}C, 1]) \\ \coprod_{\epsilon \in \{0,1\}} \mathrm{Hom}_{\Delta}([n], \{\epsilon\}) \times \mathrm{Hom}_{(0,\omega)\text{-cat}}(\mathrm{R}(K), C) \longrightarrow \mathrm{Hom}_{\Delta}([n], [1]) \times \mathrm{Hom}_{(0,\omega)\text{-cat}}(\mathrm{R}(K), C) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{\epsilon \in \{0,1\}} \mathrm{Hom}_{\Delta}([n], \{\epsilon\}) \longrightarrow \mathrm{Hom}_{(0,\omega)\text{-cat}}(\mathrm{R}([K, n]), [C, 1]) \end{array}$$

which directly concludes the proof.

Lemma 3.4.1.2. Let $C$ be an $(0, \omega)$-category and $n$ an integer. There is a canonical commutative square in $(0, \omega)$-cat:

$$\begin{array}{c} \coprod_{k \leq n} \mathrm{colim}_{\Delta_{/\{k\}}^2}[[n_0] \otimes C, 1] \vee [C, n_1] \longrightarrow \mathrm{colim}_{\Delta_{/\{n\}}^2}[[n_0] \otimes C, 1] \vee [C, n_1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{k \leq n} \mathrm{colim}_{\Delta_{/\{k\}}^2}[[n_0], 1] \vee [n_1] \longrightarrow 1 \star [C, n] \end{array}$$

natural in $C : (0, \omega)$-cat and $[n] : \Delta$.

Proof. In this proof, we use the Steiner theory recalled in section 1.2.1. It is sufficient to show the assertion when $C$ is a globular form, and then a fortiori, an $(0, \omega)$-category with an atomic and loop free basis. Using the equivalence between $(0, \omega)$-cat$_\mathrm{B}$ and ADC$_\mathrm{B}$ given in 1.2.1.23 and the equivalences

$$(K \otimes L)^{op} \sim L^{op} \otimes K^{op} \quad (K \otimes L)^{co} \sim L^{co} \otimes K^{co} \quad (1 \star K)^{op} \sim K^{op} \star 1$$

provided by propositions A.20 and 6.10 of [AM20], it is sufficient to construct for every augmented direct complex $K$ a natural commutative square:

$$\begin{array}{c} \coprod_{k \leq n} \mathrm{colim}_{[n_1] \star [n_0] \to \{k\}}[K, n_1] \vee [K \otimes \lambda[n_0], 1] \longrightarrow \mathrm{colim}_{[n_1] \star [n_0] \to [n]}[K, n_1] \vee [K \otimes \lambda[n_0], 1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{k \leq n} \mathrm{colim}_{[n_1] \star [n_0] \to \{k\}} \lambda[n_1] \vee [\lambda[n_0], 1] \longrightarrow [K, n] \star 1 \end{array}$$

163