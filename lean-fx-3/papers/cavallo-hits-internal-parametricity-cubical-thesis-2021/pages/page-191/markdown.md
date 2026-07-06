Function types and the extent operator 179

**Rules 9.3.1 (Extent).** We present the first rule in unary form for lack of space, but extent does preserve exact equality in each argument.

(1)

$$\begin{array}{c} \Psi \Vdash r \in \mathbf{I} \quad \Psi \setminus r, x: \mathbf{I} \Vdash A \text{ type} \quad \Psi \setminus r, x: \mathbf{I}, a: A \gg B \text{ type} \\ \Psi \Vdash M \in A[r/x] \quad (\forall \varepsilon) \Psi \setminus r, a_\varepsilon: A[\varepsilon/x] \gg N_\varepsilon \in B[\varepsilon/x, a_\varepsilon/a] \\ \hline \Psi \setminus r, a_0: A[0/x], a_1: A[1/x], \bar{a}: \text{Bridge}(x.A, a_0, a_1) \gg \bar{N} \in \text{Bridge}(x.B[\bar{a}x/a], N_0, N_1) \\ \hline \Psi \Vdash \text{extent}_r(M; a_0.N_0, a_1.N_1, a_0.a_1.\bar{a}.\bar{N}) \in B[r/x, M/a] \end{array}$$

(2)

$$\begin{array}{c} \varepsilon \in \{0, 1\} \quad \Psi, x: \mathbf{I} \Vdash A \text{ type} \quad \Psi, x: \mathbf{I}, a: A \gg B \text{ type} \\ \Psi \Vdash M \in A[\varepsilon/x] \quad (\forall \varepsilon) \Psi \setminus r, a_\varepsilon: A[\varepsilon/x] \gg N_\varepsilon \in B[\varepsilon/x, a_\varepsilon/a] \\ \hline \Psi \Vdash \text{extent}_\varepsilon(M; a_0.N_0, a_1.N_1, a_0.a_1.\bar{a}.\bar{N}) = N_\varepsilon[M/a_\varepsilon] \in B[\varepsilon/x, M/a] \end{array}$$

(3)

$$\begin{array}{c} \Psi \Vdash r \in \mathbf{I} \quad \Psi \setminus r, x: \mathbf{I} \Vdash A \text{ type} \quad \Psi \setminus r, x: \mathbf{I}, a: A \gg B \text{ type} \\ \Psi \setminus r, x: \mathbf{I} \Vdash M \in A \quad (\forall \varepsilon) \Psi \setminus r, a_\varepsilon: A[\varepsilon/x] \gg N_\varepsilon \in B[\varepsilon/x, a_\varepsilon/a] \\ \Psi \setminus r, a_0: A[0/x], a_1: A[1/x], \bar{a}: \text{Bridge}(x.A, a_0, a_1) \gg \bar{N} \in \text{Bridge}(x.B[\bar{a}x/a], N_0, N_1) \\ O := \bar{N}[M[0/x]/a_0, M[1/x]/a_1, \lambda^1 x.M/\bar{a}]r \\ \hline \Psi \Vdash \text{extent}_r(M[r/x]; a_0.N_0, a_1.N_1, a_0.a_1.\bar{a}.\bar{N}) = O \in B[M/a][r/x] \end{array}$$

We will prove these momentarily; first, though, we see that we can use extent to define the bridge of functions induced by $h$ as follows. Indeed, extent is precisely what we need.

$$\lambda^1 x.\lambda a.\text{extent}_x(a; a_0.(F_0 a_0), a_1.(F_1 a_1), a_0.a_1.p.(h a_0 a_1 p))$$

*Proof (of Rules 9.3.1).* As usual, we prove the reduction rules first.

(2) Immediate by coherent head expansion.

(3) By coherent head expansion. It is easy to check that $O$ is well-typed in $B[M/a][r/x]$. Let $\Psi' \Vdash \psi \in \Psi$ be given; we are in one of two cases.

- $\mathbf{y}\psi = \varepsilon \in \{0, 1\}$. Then $\text{extent}_\mathbf{y}(M[\mathbf{y}/x]; a_0.N_0, a_1.N_1, a_0.a_1.\bar{a}.\bar{N})\psi$ reduces to the term $N_\varepsilon[M[\mathbf{y}/x]/a_\varepsilon]\psi$. By the boundary rule for bridges, the latter is equal to $O\psi$ in $B[M/a][\mathbf{y}/x]\psi$.
- $r\psi = \mathbf{y}$ for some variable $\mathbf{y}$. Then $\text{extent}_r(M[r/x]; a_0.N_0, a_1.N_1, a_0.a_1.\bar{a}.\bar{N})\psi$ reduces to the following term.

$$\bar{N}\psi[M[r/x]\psi[0/y]/a_0, M[r/x]\psi[1/y]/a_1, \lambda^1 \mathbf{y}.M[r/x]\psi/\bar{a}]\mathbf{y}$$