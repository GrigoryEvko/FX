Unpacking, this means that a Kan fibration $f \colon Y \twoheadrightarrow X$ can be equipped with a uniform lifting function $i_{c,\zeta}$ as below:

$$\begin{array}{c} B \cup D \times I \xrightarrow{\alpha \cup_{\alpha} \alpha \times I} A \cup C \times I \xrightarrow{\langle y, z \rangle} Y \\ \langle [\zeta \alpha], d \times 1 \rangle \Biggl \downarrow \quad \begin{array}{c} \lrcorner \\ \downarrow \\ i_{d,\zeta\alpha}(y\alpha, z(\alpha \times I), x(\alpha \times I)) \\ \downarrow \\ B \times I \xrightarrow{\alpha \times I} A \times I \xrightarrow{x} X. \end{array} \Biggl \downarrow f \end{array}$$

Our task is to equip a uniform fibration ($f \colon Y \twoheadrightarrow X, i_{c,e}$) with the structure of an equivariant fibration. To do so, we make use of a map

$$\gamma_{\wedge} \colon I^k \times I \to I^k \qquad \gamma_{\wedge}(x_1, \dots, x_k, e) := (x_1 \wedge e, \dots, x_k \wedge e),$$

that restricts along $\{0\} \mapsto I$ to the constant map at $\vec{0} \in I^k$ and restricts along $\{1\} \mapsto I$ to the identity. This “min connection” exists because we are working with triangulated cubes in the category of simplicial sets, rather than with cartesian cubes.$^{12}$ For any $\zeta \colon A \to I^k$, the composite

$$\gamma_{\wedge} \zeta := A \times I \xrightarrow{\zeta \times I} I^k \times I \xrightarrow{\gamma_{\wedge}} I^k$$

defines a homotopy from the constant map $\vec{0} \colon A \to I^k$ to $\zeta$. We frequently pair this contracting homotopy with the map that records the coordinates from $A$, which we abbreviate as:

$$\vec{\gamma_{\wedge}} \zeta := A \times I \xrightarrow{(\pi, \gamma_{\wedge} \zeta)} A \times I^k.$$

The uniform fibration structure of $f$ provides a solution to the lifting problem

$$\begin{array}{c} A \times \{1\} \cup_{C \times \{1\}} C \times I \xrightarrow{A \cup \vec{\gamma_{\wedge}} \zeta c} A \cup C \times I^k \xrightarrow{\langle y, z \rangle} Y \\ \downarrow_{c \times \partial_1} \quad \downarrow_{i_{c,1}(z\vec{\gamma_{\wedge}} \zeta c, y, x\vec{\gamma_{\wedge}} \zeta)} \quad \downarrow_{\langle [\zeta], c \times I^k \rangle} \\ A \times I \xrightarrow{\vec{\gamma_{\wedge}} \zeta} A \times I^k \xrightarrow{x} X. \end{array}$$

This gives rise to a new lifting problem

$$\begin{array}{c} A \cup C \times I^k \to \left( C \times I^k \times I \cup_{C \times I} A \times I \right) \bigcup_{C \times I^k \times \{0\} \cup_{C \times \{0\}} A \times \{0\}} A \times I^k \times \{0\} \xrightarrow{A \times ! \times I} A \times I \xrightarrow{i_{c,1}(\cdots)} Y \\ \langle [\zeta], c \times I^k \rangle \Biggl \downarrow \quad \begin{array}{c} \lrcorner \\ \downarrow \\ \langle [\zeta], c \times I^k \rangle \hat{\times} \partial_0 \\ \downarrow \\ A \times I^k \times \{1\} \xrightarrow{A \times I^k \times \partial_1} A \times I^k \times I \xrightarrow{i_{\langle c \times I^k, [\zeta] \rangle, 0} (i_{c,1}(\cdots)!, x\gamma_{\wedge})} A \times I^k \xrightarrow{x} X, \end{array} \Biggl \downarrow f \end{array}$$

which restricts to the original lifting problem. Thus, we define $j_{c,\zeta}(y, z, x)$ to be the composite

$$j_{c,\zeta}(y, z, x) := i_{\langle c \times I^k, [\zeta] \rangle, 0} (i_{c,1}(z\vec{\gamma_{\wedge}} \zeta c, y, x\vec{\gamma_{\wedge}} \zeta)!, x\gamma_{\wedge}) \cdot (A \times I^k \times \partial_1).$$

It remains to verify that

$$j_{c,\zeta}(y, z, x) \cdot (\alpha \times \sigma^{-1}) = j_{d,\sigma\zeta\alpha}(y\alpha, z(\alpha \times \sigma^{-1}), x(\alpha \times \sigma^{-1})).$$

$^{12}$We could equally use the “max connection” to obtain a map that restricts along $\{0\} \mapsto I$ to the identity and restricts along $\{1\} \mapsto I$ to the constant map at $\vec{1} \in I^k$.

66