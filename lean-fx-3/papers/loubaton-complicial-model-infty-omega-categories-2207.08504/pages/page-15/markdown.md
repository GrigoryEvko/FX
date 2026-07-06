1.1. BASIC CONSTRUCTIONS

Definition 1.1.1.8. Let $n$ be a non null integer. A $n$-cells $f : s \to t$ is an equivalence if there exists $n$-cells $g : t \to s$ and $g' : t \to s$ such that

$$f \circ_{n-1} g = \mathbb{I}_t \qquad g \circ_{n-1} f = \mathbb{I}_s$$

Definition 1.1.1.9. A $(0, \omega)$-category is an $\omega$-category whose only equivalences are the identities. These objects are called Gaunt $\omega$-categories in [BSP21] and rigid $\omega$-categories in [Rez10]. Remark that $(0, \omega)$-categories are stable under suspensions and dualities.

We denote by $(0, \omega)$-cat the full subcategory of $\omega$-cat whose objects are the $(0, \omega)$-categories.

Definition 1.1.1.10. Let $n$ be an integer. An $(0, n)$-category is an $(0, \omega)$-category whose cell of dimension strictly higher than $n$ are units. The category of $n$-categories is denoted by $(0, n)$-cat and is the full subcategory of $(0, \omega)$-cat whose objects are $(0, n)$-categories.

Construction 1.1.1.11. Remark that the category $(0, n)$-cat is the localization of $(0, \omega)$-cat along morphisms $\mathbf{D}_k \to \mathbf{D}_n$ for $k \ge n$. We then have for any $n$ an adjunction

$$i_n : (0, n)\text{-cat} \xrightarrow{\perp} (0, \omega)\text{-cat} : \tau_n$$

The right adjoint is called the $n$-truncation.

Construction 1.1.1.12. For any $n$, we define the colimit preserving functor $\tau_n^i : (0, \omega)\text{-cat} \to (0, n)\text{-cat}$, called the intelligent $n$-truncation, sending $\mathbf{D}_k$ on $\mathbf{D}_{\min(n,k)}$. The functor $\tau_n^i$ fits in an adjunction

$$\tau_n^i : (0, \omega)\text{-cat} \xrightarrow{\perp} (0, n)\text{-cat} : i_n$$

Notation 1.1.1.13. We will identify objects of $(0, n)$-cat with their image in $(0, \omega)$-cat and we will then also note by $\tau_n$ and $\tau_n^i$ the composites $i_n \tau_n^i$ and $i_n \tau_n^i$.

Remark 1.1.1.14. The family of truncation functor induces a sequence

$$\dots \to (0, n+1)\text{-cat} \xrightarrow{\tau_n} (0, n)\text{-cat} \to \dots \to (0, 1)\text{-cat} \xrightarrow{\tau_0} (0, 0)\text{-cat}.$$

The canonical morphism

$$(0, \omega)\text{-cat} \to \lim_{n:\mathbb{N}} (0, n)\text{-cat},$$

that sends an $(0, \omega)$-category $C$ to the sequence $(\tau_n C, \tau_n \tau_{n+1} C \cong \tau_n C)$, has an inverse given by the functor

$$\underset{\mathbb{N}}{\text{colim}} : \lim_{n:\mathbb{N}} (0, n)\text{-cat} \to (0, \omega)\text{-cat}$$

that sends a sequence $(C_n, \tau_n C_{n+1} \cong C_n)$ to the colimit of the induced sequence:

$$i_0 C_0 \to i_1 C_1 \to \dots \to i_n C_n \to \dots$$

We then have an equivalence

$$(0, \omega)\text{-cat} \cong \lim_{n:\mathbb{N}} (0, n)\text{-cat}.$$

15