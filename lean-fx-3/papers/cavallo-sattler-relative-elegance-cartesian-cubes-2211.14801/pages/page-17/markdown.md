Relative Elegance and Cartesian Cubes with One Connection

17

Definition 3.14 Given $f: A \to B$ in a finitely cocomplete category with a functorial cylinder and $k \in \{0, 1\}$, we write $\mathrm{M}_k(f)$ for its $k$-sided mapping cylinder, defined as the pushout

$$\begin{array}{c} A \xrightarrow {f} B \\ \delta_ {k} \otimes A \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbb {I} \otimes A \xrightarrow [ t _ {0} ]{} \mathrm {M} _ {k} (f) \end{array}$$

The $k$-sided mapping cylinder factorization of $f$ is the factorization

$$A \xrightarrow {\iota_ {0} (\delta_ {1 - k} \otimes A)} \mathrm{M} _ {k} (f) \xrightarrow {[ f (\varepsilon \otimes A) , \mathrm{id} ]} B.$$

Definition 3.15 A cylindrical premodel structure on a finitely complete and cocomplete category $\mathbf{E}$ consists of a premodel structure and adjoint functorial cylinder on $\mathbf{E}$ such that

- the (cofibration, trivial fibration) and (trivial cofibration, fibration) weak factorization systems are cylindrical;
- $\delta_{k} \otimes (-)$ sends cofibrations to trivial cofibrations for $k \in \{0, 1\}$.

Remark 3.16 The above conditions are transpose to equivalent dual conditions on the corresponding adjoint functorial path object. Like its constituent components, the notion of cylindrical premodel structure is thus self-dual: a cylindrical premodel structure on $\mathbf{E}$ is the same as a cylindrical premodel structure on $\mathbf{E}^{\mathrm{op}}$.

Remark 3.17 (Stability under (co)slicing) Continuing Remarks 3.2 and 3.11, a cylindrical premodel structure on $\mathbf{E}$ descends to cylindrical premodel structures on slices and coslices of $\mathbf{E}$. We may exploit this to simplify arguments by for example working in a slice.

Fix once more a premodel category $\mathbf{M}$ with factorization systems $(\mathcal{C},\mathcal{F}_t)$ and $(\mathcal{C}_t,\mathcal{F})$. We show that condition $\mathbf{C}$ is reducible to condition $\mathbf{A}$ when $\mathbf{M}$ is cylindrical by relating trivial fibrations with dual strong deformation retracts.

Definition 3.18 In a category with a functorial cylinder, we say $f: Y \to X$ is a dual strong $k$-oriented deformation retract for some $k \in \{0, 1\}$ when we have a map $s: X \to Y$ such that $f s = \mathrm{id}$ and a homotopy $h: \mathbb{I} \otimes Y \to Y$ such that $h(\delta_k \otimes Y) = sf, h(\delta_{1-k} \otimes Y) = \mathrm{id}$, and $f h$ is a constant homotopy. Equivalently (if the category is finitely cocomplete), $f$ is a dual strong $k$-oriented deformation retract when we have a diagonal filler

$$\begin{array}{c} Y \xrightarrow {=} Y \\ \iota_ {0} (\delta_ {1 - k} \otimes Y) \Biggl \downarrow \\ \mathrm{M} _ {k} (f) \xrightarrow [ [ f (\varepsilon \otimes Y) , \mathrm{id} ] ]{} X. \end{array}$$

The following is a standard construction (see, e.g., [Qui67, Lemma I.5.1]).

2025/10/16 00:43