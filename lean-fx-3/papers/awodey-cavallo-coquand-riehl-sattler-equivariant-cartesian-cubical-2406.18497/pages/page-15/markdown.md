Recall from [Shu19, 2.8] the bicategorical notion of lifting property in a 2-category K: morphisms $i: A \to B$ and $f: Y \to X$ have the lifting property when the map $\mathsf{K}(B, Y) \to \mathsf{K}(A, Y) \times_{\mathsf{K}(A, X)}^h \mathsf{K}(B, X)$ is essentially surjective, where $\times^h$ is a weak bicategorical pullback.

**Definition 2.1.8** ([Shu19, 5.1]). A morphism in contravariant groupoid-valued pseudofunctors on $\mathsf{E}$ is an **acyclic fibration** if it right lifts bicategorically against images of monomorphisms under the Yoneda embedding.

*Remark 2.1.9.* For strict discrete fibrations in contravariant groupoid-valued pseudofunctors on $\mathsf{E}$, the bicategorical right lifting property is equivalent to the categorical right lifting property [Shu19, 2.10]. In particular, this applies to notions of fibred structure and their pullbacks.

**Lemma 2.1.10.** *Given a notion of fibred structure $\psi: \mathfrak{F} \to \mathfrak{E}$, the following conditions are equivalent:*

(i) $\psi: \mathfrak{F} \to \mathfrak{E}$ is relatively acyclic,

(ii) each kernel pair projection of $\psi$ is an acyclic fibration.

*Proof.* For a diagram

$$\begin{array}{c} Y' \xrightarrow{i'} Y \\ f' \downarrow \quad \downarrow \quad \downarrow f \\ X' \xrightarrow{i} X, \end{array} \tag{2.1.11}$$

a pair of $\mathfrak{F}$-algebra structures on $f$ and $f'$ consists of a pair of maps $x: \mathsf{E}(-, X) \to \mathfrak{F}$ and $x': \mathsf{E}(-, X') \to \mathfrak{F}$ such that the outer square

$$\begin{array}{c} \mathsf{E}(-, X') \xrightarrow{\quad} \mathfrak{F} \times_{\mathfrak{E}} \mathfrak{F} \xrightarrow{\quad} \mathfrak{F} \\ i \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ \mathsf{E}(-, X) \xrightarrow{\quad} \mathfrak{F} \xrightarrow{\quad} \mathfrak{F}, \end{array}$$

commutes, i.e., corresponds to a lifting problem against the kernel pair of $\psi$. A solution to such a lifting problem is determined by a map $\overline{x}: \mathsf{E}(-, X) \to \mathfrak{F}$ such that $\overline{x}i = x'$ and $\psi\overline{x} = \psi x$, which is to say an $\mathfrak{F}$-algebra structure on $f$ such that (2.1.11) is an $\mathfrak{F}$-morphism from $x'$ to $\overline{x}$. $\square$

**Lemma 2.1.12.** *When $\mathfrak{F}$ is a locally representable and relatively acyclic notion of fibred structure on $\mathsf{E}$ then for any map $f: Y \to X$ the maps in the kernel pair of $\psi_f: \mathfrak{F}(f) \to X$ lift against monomorphisms in $\mathsf{E}$.*

*Proof.* Recall the definition of the maps in question:

$$\begin{array}{c} \mathsf{E}(-, \mathfrak{F}(f)) \longrightarrow \mathfrak{F} \\ \psi_f \downarrow \quad \downarrow \quad \downarrow \psi \\ \mathsf{E}(-, X) \xrightarrow{f} \mathfrak{E}. \end{array}$$

As the kernel pair of a pullback is the pullback of the kernel pair, the kernel pair of the representable map $\psi_f: \mathsf{E}(-, \mathfrak{F}(f)) \to \mathsf{E}(-, X)$ lifts against representable monomorphisms. But since the Yoneda embedding is fully faithful and preserves limits, this means that the kernel pair of the map $\psi_f: \mathfrak{F}(f) \to X$ lifts against monomorphisms in $\mathsf{E}$. $\square$

By Lemma 2.1.10, a full notion of fibred structure, such as the following example, is automatically relatively acyclic.

15