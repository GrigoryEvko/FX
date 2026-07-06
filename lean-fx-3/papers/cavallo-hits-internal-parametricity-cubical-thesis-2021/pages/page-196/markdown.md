184

Parametric cubical type theory

$\mathrm{gel}_x(M'_{\mathrm{id}_\psi}, N'_{\mathrm{id}_\psi}, P'_{\mathrm{id}_\psi}) \in \mathrm{Gel}_x(A_0, A_1, R)$. We combine this with the above to get that $\mathrm{gel}_x(M_{\mathrm{id}_\psi}, N_{\mathrm{id}_\psi}, P_{\mathrm{id}_\psi})$ is equal to $\mathrm{gel}_x(M'_{\mathrm{id}_\psi}, N'_{\mathrm{id}_\psi}, P'_{\mathrm{id}_\psi})$ at the Gel type, which implies that $P_{\mathrm{id}_\psi}$ is equal to $P'_{\mathrm{id}_\psi}$; the result follows by transitivity.

The second rule is immediate by coherent expansion. For the third rule, we apply Lemma 3.1.36 to see that $Q$ is equal to some gel value. The equation then follows by previously proven rules for gel. $\square$

It is worth interrogating the difference in form between the V types of Section 3.1.6.2 and the new Gel types. In contrast to Gel, which simply converts a relation into a bridge of types, V extends an existing path of types by an isomorphism, as shown below.

$$
\begin{array}{c}
A \\
I \quad \Downarrow \\
B[0/x] \xrightarrow[B]{} B[1/x] \\
x \rightarrow
\end{array}
$$

The formulation of Gel is unavailable for V because path dimensions are structural: we cannot forbid the path interval variable from occurring in the other arguments, except in a sense by hypothesizing $x \equiv 0$ or $x \equiv 1$. We cannot put *all* of the inputs under one of these assumptions, as then we would have no type at the other endpoint! So we allow the argument $B$ to depend on the variable. This is not a problem for univalence, because we always have the *option* of supplying a degenerate $B$—we are merely unable to *enforce* degeneracy. Note however that, conversely, a V-like type former would be insufficient for relativity. In the world of paths, we know that a degenerate path of types corresponds to the identity isomorphism, so composing with a degenerate path is a way of converting an isomorphism into a path. But *a degenerate bridge of types does not necessarily correspond to the identity relation*. Indeed, according to the formulation of relativity, a degenerate bridge of types $B$ corresponds instead to the bridge relation $\mathrm{Bridge}(B, -, -)$, which can be distinct from the identity relation $\mathrm{Path}(B, -, -)$. The canonical example, of course, is $B := \mathrm{U}$.

*Remark 9.4.5.* Our Gel types are weaker than the equivalent introduced in [BCM15], our sole departure from their blueprint. They require that the equation

$$
\mathrm{Bridge}(x.\mathrm{Gel}_x(A_0, A_1, a_0.a_1.R), M_0, M_1) = R[M_0/a_0, M_1/a_1] \text{ type}
$$

hold up to *exact equality*, while for us this only holds up to an isomorphism. Note that we need this equation up to a path in order to show that Bridge and Gel are inverse, thus for relativity. In a cubical type theory, we can rely on univalence to turn the isomorphism into the necessary path. Without univalence, one must instead posit an exact