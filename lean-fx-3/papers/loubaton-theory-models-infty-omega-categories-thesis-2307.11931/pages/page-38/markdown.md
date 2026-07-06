CHAPTER 1. THE CATEGORY OF $(0, \omega)$-CATEGORIES

For an integer $n$, we define by induction the functor $\Sigma^n : \mathrm{Psh}(\mathrm{G}) \to \mathrm{Psh}(\mathrm{G})$ with the formula:

$$\Sigma^0 := id \qquad \Sigma^{n+1} := \Sigma^n[\_, 1].$$

**1.1.1.7.** Let $n$ be a non null integer. A $n$-cells $f : s \to t$ is an *equivalence* if there exists $n$-cells $g : t \to s$ and $g' : t \to s$ such that

$$f \circ_{n-1} g = \mathbb{I}_t \qquad g \circ_{n-1} f = \mathbb{I}_s$$

A $(0, \omega)$-category is an $\omega$-category whose only equivalences are the identities. These objects are called *Gaunt $\omega$-categories* in [BSP21] and *rigid $\omega$-categories* in [Rez10]. Remark that $(0, \omega)$-categories are stable under suspensions and dualities. We then define $(0, \omega)$-cat as the full subcategory of $\omega$-cat whose objects are the $(0, \omega)$-categories.

**1.1.1.8.** Let $n$ be an integer. An $(0, n)$-category is an $(0, \omega)$-category whose cell of dimension strictly higher than $n$ are units. The category of $n$-categories is denoted by $(0, n)$-cat and is the full subcategory of $(0, \omega)$-cat whose objects are $(0, n)$-categories.

Remark that the category $(0, n)$-cat is the localization of $(0, \omega)$-cat along morphisms $\mathbf{D}_k \to \mathbf{D}_n$ for $k \geq n$. We then have for any $n$ an adjunction

$$i_n : (0, n)\text{-cat} \xrightarrow[\downarrow]{} (0, \omega)\text{-cat} : \tau_n$$

The right adjoint is called the $n$-truncation. For any $n$, we define the colimit preserving functor $\tau_n^i : (0, \omega)\text{-cat} \to (0, n)\text{-cat}$, called the *intelligent $n$-truncation*, sending $\mathbf{D}_k$ on $\mathbf{D}_{\min(n,k)}$. The functor $\tau_n^i$ fits in an adjunction

$$\tau_n^i : (0, \omega)\text{-cat} \xrightarrow[\downarrow]{} (0, n)\text{-cat} : i_n$$

We will identify objects of $(0, n)$-cat with their image in $(0, \omega)$-cat and we will then also note by $\tau_n$ and $\tau_n^i$ the composites $i_n \tau_n^i$ and $i_n \tau_n^i$.

**1.1.1.9.** The family of truncation functor induces a sequence

$$\dots \to (0, n+1)\text{-cat} \xrightarrow{\tau_n} (0, n)\text{-cat} \to \dots \to (0, 1)\text{-cat} \xrightarrow{\tau_0} (0, 0)\text{-cat}.$$

The canonical morphism

$$(0, \omega)\text{-cat} \to \lim_{n \in \mathbb{N}} (0, n)\text{-cat},$$

that sends an $(0, \omega)$-category $C$ to the sequence $(\tau_n C, \tau_n \tau_{n+1} C \cong \tau_n C)$, has an inverse given by the functor

$$\operatorname{colim}_{\mathbb{N}} : \lim_{n \in \mathbb{N}} (0, n)\text{-cat} \to (0, \omega)\text{-cat}$$

28