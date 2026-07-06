lattices $NDL$; these are distributive lattices $D$ with the additional property that for any $a, b \in D$ if $a \vee b = 1$ then there exists $a', b' \in D$ such that $a' \wedge b = 0$ and $a' \vee b = 1 = a \vee b'$. We write **NDL** for the category of normal distributive lattices with lattice homomorphisms as morphisms. We will not need to be explicit about the underlying lattice theory here as we shall instead quote:

**Proposition 2.1** (i) There is an essentially surjective functor $c : \mathbf{NDL} \longrightarrow \mathbf{KHaus}^{op}$ to the opposite of the category of compact Hausdorff locales.

(ii) The functor (i) can be constructed relative to any topos and is stable under geometric morphisms. That is, if $f : \mathcal{F} \longrightarrow \mathcal{E}$ is a geometric morphism and $D$ is a normal distributive lattice in $\mathcal{E}$, then $f^*(c_{\mathcal{E}}(D)) \cong c_{\mathcal{F}}(f^*D)$ where we are using $f^*$ both for the locale pullback functor $\mathbf{Loc}_{\mathcal{E}} \longrightarrow \mathbf{Loc}_{\mathcal{F}}$ and the inverse image of the geometric morphism $f$.

*Proof:* Part (i) is covered in [HT22], but is also essentially covered in [SVW14]. Any compact Hausdorff locale $X$ is isomorphic to $c(\mathcal{O}(X))$, where $\mathcal{O}(X)$ is the frame of opens of $X$ (which is a normal distributive lattice if $X$ is compact Hausdorff).

Consult [SVW14] for (ii).

### 3 Stacks on Loc

In this section we recall the notion of stack on the category of locales, where our notion of cover is a single morphism consisting of an effective descent morphism. We also give some examples of localic stacks.

**Definition 3.1** Given a pseudo-functor $M : \mathbf{Loc}^{op} \longrightarrow \mathfrak{CAT}$ for any locale map $f : Y \longrightarrow X$ we define the category $Des(M, f)$ of descent data for $f$ in $\mathcal{C}$ as follows. The objects of $Des(M, f)$ are pairs $(A, \theta_A) : M(\pi_1)(A) \longrightarrow M(\pi_2)(A)$, where $A$ is an object of $M(Y)$, $\theta_A$ satisfies the cocycle conditions for $f$ and $\pi_1, \pi_2$ are the two projections $X \times_Y X \longrightarrow X$. Morphisms $(A, \theta_A) \longrightarrow (B, \theta_B)$ consists of maps $\psi : A \longrightarrow B$ compatible with the $\theta_s$; that is, $[M(\pi_2)(\psi)]\theta_A = \theta_B[M(\pi_1)(\psi)]$.

See Definition B1.5.1 of [J02] for background and the preamble to Proposition B1.5.5 for the case of a single cover. Of course the morphisms $\theta_A$ are all isomorphisms: their inverses are determined by $M(\tau)(\theta_A)$ where $\tau : Y \times_X Y \longrightarrow Y \times_X Y$ is the twist isomorphism. There is a canonical functor $M(X) \longrightarrow Des(M, f)$ for any $f : Y \longrightarrow X$: send any object $A$ to $M(f)(A)$.

**Example 3.2** Consider $\mathbf{LOC} : \mathbf{Loc}^{op} \longrightarrow \mathfrak{CAT}$, the pullback pseudo-functor on $\mathbf{Loc}$ which sends any locale $X$ to the slice category $\mathbf{Loc}/X$ and any locale map $f$ to pullback along $f$; e.g. Example B1.2.2(c) of [J02]. Then $Des(\mathbf{LOC}, f : Y \longrightarrow X)$ is isomorphic to $[\mathbb{Y}_f, \mathbf{Loc}]$.

**Definition 3.3** A pseudo-functor $M : \mathbf{Loc}^{op} \longrightarrow \mathfrak{CAT}$ is a stack provided for any effective descent morphism $f : X \longrightarrow Y$, $M(Y)$ is equivalent, via the canonical functor, to $Des(M, f)$.

4