1.2. GRAY OPERATIONS

There exists a unique decomposition of $a$ as

$$a \cong a' \vee [[n] \vee [k] \vee [1] \vee [k'] \vee [n'], 1] \vee a''$$

where the cell $[[1], 1] \to a$ is $b$, and where $k$ and $k'$ are the maximal integers such that the image by the composite cell of

$$[[k] \vee [1] \vee [k'], 1] \to a$$

is 0-comparable with $x$, and such that

$$[[k], 1] \coprod [[k'], 1] \to a \to D$$

factors through $C$.

We then have

$$\Lambda^{\Gamma_0} a \cong a' \vee [[n + k] \coprod_{[k]} [k + 1 + k'] \coprod_{[k']} [k' + n'], 1] \vee a''$$

As the functor $a' \vee [\_, 1] \vee a : \mathrm{Psh}(\Delta) \to \mathrm{Psh}(\Theta)$ sends $\overline{\mathrm{W}_1}$ to $\overline{\mathrm{W}_2}$, and as

$$[n + k] \coprod_{[k]} [k + 1 + k'] \coprod_{[k']} [k' + n'] \to [n + k + 1 + k' + n']$$

is in $\overline{\mathrm{W}_1}$, this concludes the proof.

**Proposition 1.2.2.25.** *Let $C$ and $D$ be two $(0, 2)$-categories admitting loop-free and atomic bases, fitting in a cocartesian square of shape:*

$$\begin{array}{c} \partial [[1], 1] \xrightarrow{\partial x} C \\ \downarrow \qquad \qquad \qquad \downarrow f \\ [[1], 1] \xrightarrow{x} D \end{array}$$

*Then, viewed as a morphism of $\mathrm{Psh}(\Theta_2)$, the morphism $j : C \cup x \to D$ is in $\overline{\mathrm{W}_2}$.*

*Proof.* The category $\Gamma_0$ inherits from $\Theta_{/D}$ a structure of Reedy elegant category. The two functors

$$\begin{array}{c c c c c c} \Gamma_0 & \to & \mathrm{Psh}(\Delta) & \qquad \Gamma_0 & \to & \mathrm{Psh}(\Delta) \\ a \to D & \mapsto & \Lambda^{\Gamma_0} a & a \to D & \mapsto & a \end{array}$$

are Reedy cofibrant (definition 1.1.3.1). The morphism

$$C \cup x \cong \underset{\Gamma_0}{\mathrm{colim}} \, \Lambda^{\Gamma_0} a \to \underset{\Gamma_0}{\mathrm{colim}} \, \Lambda^{\Gamma_0} a$$

is then in $\overline{\mathrm{W}_2}$. We proceed similarly to demonstrate that the morphism

$$\underset{\Gamma_0}{\mathrm{colim}} \, \Lambda^{\Gamma_0} a \cong \underset{\Gamma_1}{\mathrm{colim}} \, \Lambda^{\Gamma_1} a \to \Lambda^{\Gamma_1} a \cong D$$

is in $\overline{\mathrm{W}_2}$. By stability by composition of $\overline{\mathrm{W}_2}$, this concludes the proof.

**Proposition 1.2.2.26.** *Let $C$ and $D$ be two $(0, 1)$-categories admitting loop-free and atomic bases, fitting in a cocartesian square of shape:*

$$\begin{array}{c} \partial [1] \xrightarrow{\partial x} C \\ \downarrow \qquad \qquad \qquad \downarrow f \\ [1] \xrightarrow{x} D \end{array}$$

*Then, viewed as a morphism of $\mathrm{Psh}(\Delta)$, the morphism $j : C \cup x \to D$ is in $\overline{\mathrm{W}_1}$.*

39