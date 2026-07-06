The bridge interval 169

**Definition 9.1.3 (Restriction for interval contexts).** We define the restriction of an interval context $\Psi$ by a bridge interval term $\Psi \Vdash r \in \mathbf{I}$, written $\Psi \setminus r$, as follows.

$$\begin{aligned} \Psi \setminus \mathbf{0} &:= \Psi \\ \Psi \setminus \mathbf{1} &:= \Psi \\ (\Psi, y : \mathbb{I}) \setminus \mathbf{x} &:= (\Psi \setminus \mathbf{x}), y : \mathbb{I} \\ (\Psi, \mathbf{y} : \mathbf{I}) \setminus \mathbf{x} &:= \begin{cases} \Psi & \text{if } \mathbf{x} = \mathbf{y} \\ (\Psi \setminus \mathbf{x}), \mathbf{y} : \mathbf{I} & \text{otherwise} \end{cases} \end{aligned}$$

**Definition 9.1.4 (Interval substitutions).** We extend the interval substitution judgment $\Psi' \Vdash \psi \in \Psi$, specified in Definition 3.1.4, by the following rule.

$$\frac{\Psi' \Vdash r \in \mathbf{I} \quad \Psi' \setminus r \Vdash \psi \in \Psi}{\Psi' \Vdash (\psi, r/x) \in (\Psi, x : \mathbf{I})}$$

To construct the identity substitution $x : \mathbf{I}, y : \mathbf{I} \Vdash (x/x, y/y) \in (x : \mathbf{I}, y : \mathbf{I})$, we must show that $x : \mathbf{I}, y : \mathbf{I} \setminus y \Vdash (x/x) \in (x : \mathbf{I})$, which is to say that $x : \mathbf{I} \Vdash (x/x) \in (x : \mathbf{I})$. Here we have no problem. If we try to type the forbidden “$z : \mathbf{I} \Vdash (z/x, z/y) \in (x : \mathbf{I}, y : \mathbf{I})$”, on the other hand, we find we need the evidently nonsensical “$\cdot \Vdash (z/x) \in (x : \mathbf{I})$”.

Finally, we add equations on bridge interval terms to the language of constraints. While a path constraint may identify any pair of terms, $r \equiv s$, we only allow the identification of a bridge interval term with a constant. This reflects the affine nature of these terms: the only way two bridge variables can become equal is if they both become the same constant. More practically, while the general path constraints are apparently necessary to implement coercion in V types in this theory—see the discussion of *diagonal cofibrations* in [CMS20]—such a need does not arise in the bridge theory.

**Definition 9.1.5 (Closed constraint judgments).** We extend the constraint and constraint satisfaction judgments, specified in Definition 3.1.21, by the following.

$$\frac{\Psi \Vdash r \in \mathbf{I} \quad \varepsilon \in \{0, 1\}}{\Psi \Vdash (r \equiv \varepsilon) \in \mathbb{F}} \quad \frac{\varepsilon \in \{0, 1\}}{\Psi \Vdash \varepsilon \equiv \varepsilon \text{ satisfied}}$$

Much as composition with path constraints is necessary to implement coercion in path types (Figure 3.2), we will need bridge constraints to do the same for bridge types.

In theory, these additions to the interval theory could invalidate theorems we already have proven for cubical type theory; for example, some Kan operation might rely on analyzing the shape of constraints. In practice, however, it is easy to check that this is not the case.