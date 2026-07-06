4.3. GRAY OPERATIONS

and for any pair of objects $x : C$ and $y : D$ (resp. $x : D$ and $y : C$), the outer square of the following diagram

$$
\begin{array}{c}
\hom_C(x, ry) \xrightarrow{i} \hom_D(ix, iry) \xrightarrow{\psi_{y!}} \hom_D(ix, y) \\
\downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\
\hom_{C'}(px, pr'y) \xrightarrow{i'} \hom_{D'}(p'i'x, p'i'r'y) \xrightarrow{\psi'_{p'y!}} \hom_{D'}(p'i'x, p'y)
\end{array}
$$

(resp.

$$
\begin{array}{c}
\hom_C(rx, y) \xrightarrow{i} \hom_D(irx, iy) \xrightarrow{\psi_{x!}} \hom_D(x, iy) \\
\downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\
\hom_{C'}(pr'x, py) \xrightarrow{i'} \hom_{D'}(p'i'r'x, p'i'y) \xrightarrow{\psi'_{p'x!}} \hom_{D'}(p'x, p'i'y)
\end{array}
$$

is a left (resp. right) $(k + 1)$-Gray deformation retract, whose retract is given by

$$
\begin{array}{c}
\hom_D(ix, y) \xrightarrow{r} \hom_C(x, ry) \\
\downarrow \qquad \qquad \qquad \downarrow \\
\hom_{D'}(p'i'x, p'y) \xrightarrow{r'} \hom_{C'}(px, pr'y)
\end{array}
$$

$$
\begin{array}{c}
(\text{resp.} \hom_D(x, iy) \xrightarrow{r} \hom_C(rx, y) \\
\downarrow \qquad \qquad \qquad \downarrow \\
\hom_{D'}(p'x, p'i'y) \xrightarrow{r'} \hom_{C'}(pr'x, py)
\end{array}
$$

Proof. This comes from the fact that the construction of the retraction and the deformation in the previous proposition was functorial. $\square$

**Proposition 4.3.2.11.** If $i$ is a left $k$-Gray deformation retract, $[i, 1]$ is a right $(k + 1)$-Gray deformation retract. Conversely, if $i$ is a right $k$-Gray deformation retract, $[i, 1]$ is a left $(k + 1)$-Gray deformation retract morphism.

Proof. Let $(i : C \to D, r, \phi)$ be a left $k$-Gray deformation retract structure. We define the morphism $\psi : [D, 1] \otimes_{k+1} [1] \to [D, 1]$ as the horizontal colimit of the following diagram:

$$
\begin{array}{c}
[1] \vee [D, 1] \longleftarrow [D \otimes_k \{0\}, 1] \longrightarrow [D \otimes_k [1], 1] \longleftarrow [D \otimes_k \{1\}, 1] \longrightarrow [D, 1] \vee [1] \\
\searrow \xrightarrow{[r, 1] \downarrow} [C, 1] \xrightarrow{[i, 1]} [D, 1] \xleftarrow{[\phi, 1] \downarrow} [D, 1] \xleftarrow{\downarrow [id, 1]} [D, 1]
\end{array}
$$

Eventually, remark that the triple $([i, 1], [r, 1], \psi)$ is a right $(k + 1)$-Gray deformation retract. The other assertion is demonstrated similarly. $\square$

**Proposition 4.3.2.12.** For any integer $n$, if $n$ is even, $i_n^- : \mathbf{D}_n \to \mathbf{D}_{n+1}$ is a left $n$-Gray deformation retract and $i_n^+ : \mathbf{D}_n \to \mathbf{D}_{n+1}$ is a right $n$-Gray deformation retract, and if $n$ is odd, $i_n^-$ is a right $n$-Gray deformation retract and $i_n^+$ is a left $n$-Gray deformation retract.

215