3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

By construction, if $[n_0]^{op} \star [n_1] \to [n]$ factor through $\{p\}$ for $p \leq n$ we have a commutative diagram

$$\begin{array}{c} [[n_2] \otimes [n_0] \otimes a, 1] \vee [[n_0] \otimes a, n_3] \longrightarrow H^2(a, n) \\ \downarrow \hspace{2em} \downarrow \\ [[n_2] \otimes [n_0] \otimes e, 1] \vee [[n_0] \otimes e, n_3] \longrightarrow e \star \{p\} \longrightarrow e \star [a, n] \end{array}$$

If $[n_2]^{op} \star [n_3] \to [1+n_1]$ factors through $\{0\}$, $\tilde{n}_3$ is equal to $-1$, and we have a commutative diagram

$$\begin{array}{c} [[n_2] \otimes [n_0] \otimes a, 1] \vee [[n_0] \otimes a, n_3] \longrightarrow H^2(a, n) \\ \downarrow \hspace{2em} \downarrow \\ [[n_2] \otimes e, 1] \vee [e, n_3] \longrightarrow e \star \emptyset \longrightarrow e \star [a, n] \end{array}$$

and if $[n_2]^{op} \star [n_3] \to [1+n_1]$ factors through any other point, $\tilde{n}_3$ is equal to 0, and we have a commutative diagram

$$\begin{array}{c} [[n_2] \otimes [n_0] \otimes a, 1] \vee [[n_0] \otimes a, n_3] \longrightarrow H^2(a, n) \\ \downarrow \hspace{2em} \downarrow \\ [[n_2] \otimes e, 1] \vee [e, n_3] \longrightarrow e \star \{k\} \longrightarrow e \star [a, n] \end{array}$$

where $k$ is the image of the composite morphism $[\tilde{n}_2]^{op} \star [\tilde{n}_3] \to [n_1] \to [n]$. The cocartesian square (3.3.1.2) then implies that $H^2(a, n)$ lifts to a natural transformation

$$s^0 \star [a, n] : e \star e \star [a, n] \to e \star [a, n].$$

By extension by colimits, this induces a natural transformation

$$C \mapsto (s^0 \star C : e \star e \star C \to e \star C).$$

To define the cosimplicial object, we will need to show the commutativity of several diagrams whose initial objects are of shape $e \star .. \star e \star [a, n]$. To this extend, it is enough to find coverings of these objects by easier one, and to show that the induced diagrams commute.

**Lemma 3.3.1.3.** We set $\Pi^0_{/[n]} := \Delta^2_{/[n]}$ and

$$\Pi^k_{/[n]} := \underset{\Delta^2_{/[n]}}{\text{colim}} \underset{\Delta^2_{/[n_1+1]}}{\text{colim}} \dots \underset{\Delta^2_{/[n_{2k-1}+1]}}{\text{colim}} \Delta^2_{/[n_{2k+1}+1]}$$

There is an epimorphism:

$$\underset{\Pi^k_{/[n]} \times A}{\text{colim}} [[n_{2k}] \otimes [n_{2k-2}] \otimes ... \otimes [n_0] \otimes a, 1 + n_{2k-1}] \to \underbrace{e \star e \star ... \star e}_{k+1} \star [a, n]$$

139