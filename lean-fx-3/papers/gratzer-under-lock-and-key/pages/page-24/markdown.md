CASE(Γ, ℍ_μ, Δ ⊢ let_ρ mod_ξ(x_A) ← M in N : B @ p).

Suppose ρ : q → p. We then know that

$$\begin{array}{l} \Gamma, \text{ℍ}_\mu, \Delta, \text{ℍ}_\rho \vdash M : \langle \xi \mid A \rangle @ q \\ \Gamma, \text{ℍ}_\mu, \Delta, x : (\rho \circ \xi \mid A) \vdash N : B @ p \end{array}$$

Then by the IH we have that

$$\begin{array}{l} \Gamma, \text{ℍ}_\nu, \Delta, \text{ℍ}_\rho \vdash M[\Gamma; \alpha; \Delta, \text{ℍ}_\rho] : \langle \xi \mid A \rangle @ p \\ \Gamma, \text{ℍ}_\nu, \Delta, x : (\rho \circ \xi \mid A) \vdash N[\Gamma; \alpha; \Delta, x : (\rho \circ \xi \mid A)] : B @ q \end{array}$$

so by a single application of LET we have

$$\Gamma, \text{ℍ}_\nu, \Delta \vdash \text{let}_\rho \text{ mod}_\xi(x_A) \leftarrow M[\Gamma; \alpha; \Delta, \text{ℍ}_\rho] \text{ in } N[\Gamma; \alpha; \Delta, x : (\rho \circ \xi \mid A)] : B @ p$$

But this term is by definition equal to (let_ρ mod_ξ(x_A) ← M in N)[Γ; α; Δ].

CASE(Γ, ℍ_μ, Δ ⊢ λx : (ξ | A). M : (ξ | A) → B @ p).

We know that

$$\Gamma, \text{ℍ}_\nu, \Delta, x : (\xi \mid A) \vdash M : B @ p$$

By the IH we have that

$$\Gamma, \text{ℍ}_\nu, \Delta, x : (\xi \mid A) \vdash M[\Gamma; \alpha; \Delta, x : (\xi \mid A)] : B @ p$$

So, as

$$(\lambda x : (\xi \mid A). M)[\Gamma; \alpha; \Delta] \stackrel{\text{def}}{=} \lambda x : (\mu \mid A). M[\Gamma; \alpha; \Delta, x : (\xi \mid A)]$$

the result follows by an application of LAM.

CASE(Γ, ℍ_μ, Δ ⊢ M(N)_ξ : B @ b).

Writing ξ : a → b, we know that

$$\begin{array}{l} \Gamma, \text{ℍ}_\mu, \Delta \vdash M : (\xi \mid A) \rightarrow B @ b \\ \Gamma, \text{ℍ}_\mu, \Delta, \text{ℍ}_\xi \vdash N : A @ a \end{array}$$

By the IH, we obtain

$$\begin{array}{l} \Gamma, \text{ℍ}_\nu, \Delta \vdash M[\Gamma; \alpha; \Delta] : (\xi \mid A) \rightarrow B @ b \\ \Gamma, \text{ℍ}_\nu, \Delta, \text{ℍ}_\xi \vdash N[\Gamma; \alpha; \Delta, \text{ℍ}_\xi] : A @ a \end{array}$$

By a single application of APP we obtain

$$\Gamma, \text{ℍ}_\nu, \Delta \vdash (M[\Gamma; \alpha; \Delta])(N[\Gamma; \alpha; \Delta, \text{ℍ}_\xi])_\xi : B @ b$$

and as this term is exactly the definiens of (M(N)_ξ)[Γ; α; Δ] we obtain the result.

24