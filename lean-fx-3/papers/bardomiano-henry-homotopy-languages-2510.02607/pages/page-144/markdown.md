## C.1 Review

**Definition C.1.** A *weak model category* is a category $\mathcal{M}$ with three classes of maps: *cofibrations*, *fibrations* and *weak equivalences* satisfying the following conditions:

1. $\mathcal{M}$ has an initial object 0 and a terminal object 1, the identity of 0 is a cofibration, the identity of 1 is a fibration.
2. A composite of cofibrations with cofibrant domain is a cofibration. A composite of fibrations with fibrant codomain is a fibration.
3. Given two composable arrows $X \xrightarrow{f} Y \xrightarrow{g} Z$ where each of $X, Y$ and $Z$ are fibrant or cofibrant, if two of $f, g, g \circ f$ are weak equivalences, then the third is also a weak equivalence.
4. Every isomorphism between objects that are either fibrant or cofibrant is a weak equivalence.
5. Given a solid diagram:

$$\begin{array}{c} A \longrightarrow B \\ \downarrow i \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

Where $i$ is a cofibration and $A$ and $B$ are cofibrant, then the pushout $j$ exists and is a cofibration.

6. The dual of condition 5 holds for fibrations between fibrant objects.
7. Every arrow isomorphic to a fibration, cofibration, or weak equivalence is also one.
8. Every arrow from a cofibrant to a fibrant object can be factored as a cofibration followed by a trivial fibration.
9. Every arrow from a cofibrant to a fibrant object can be factored as a trivial cofibration followed by a fibration.
10. Given a solid square:

$$\begin{array}{c} A \longrightarrow X \\ \downarrow i \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

144