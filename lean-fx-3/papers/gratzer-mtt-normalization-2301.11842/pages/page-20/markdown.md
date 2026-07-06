27:20

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

4.1. Synthetic Tait computability. For this subsection, fix two presheaf topoi $\mathcal{E}$ and $\mathcal{F}$ along with a continuous functor $\rho : \mathcal{E} \longrightarrow \mathcal{F}$.

Definition 4.1. The Artin gluing $\mathbf{Gl}(\rho)$ is a category whose objects are triples $(E, F, f)$ of an object from $\mathcal{E}$, an object from $\mathcal{F}$, and a morphism $F \longrightarrow \rho(E)$. Morphisms in $\mathbf{Gl}(\rho)$ are commuting squares:

$$\begin{array}{c} F_0 \xrightarrow{\alpha} F_1 \\ f_0 \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \rho(E_0) \xrightarrow{\rho(\beta)} \rho(E_1) \end{array}$$

Projection induces functors $\pi_0 : \mathbf{Gl}(\rho) \longrightarrow \mathcal{E}$ and $\pi_1 : \mathbf{Gl}(\rho) \longrightarrow \mathcal{F}$.

Example 4.2. Intuitively $\mathbf{Gl}(\rho)$ is a category of proof-relevant $\mathcal{F}$-predicates on $\rho$-elements of $\mathcal{E}$. To cultivate this intuition, consider $\mathcal{F} = \mathbf{Set}$ and $\rho = [\mathbf{1}, -]$. An object of $\mathbf{Gl}([\mathbf{1}, -])$ is a triple of $(S, E, f)$ which induces a proof-relevant predicate $\Phi(e) = f^{-1}(e)$ on the global points of $E$. Following Tait [Tai67], we refer to elements in the image of $f$ as computable elements. Morphisms are then morphisms of $\mathcal{E}$ equipped with additional structure ensuring that computable elements are sent to computable elements.

We now reap the first reward from considering proof-relevant predicates: $\mathbf{Gl}(\rho)$ is extremely well-behaved.

Theorem 4.3 [AGV72, CJ95]. $\mathbf{Gl}(\rho)$ is a presheaf topos and $\pi_0$ is a logical functor with left and right adjoints.

As a presheaf topos, $\mathbf{Gl}(\rho)$ enjoys a model of extensional type theory with a strictly cumulative hierarchy of universes and a universe of propositions $\Omega$. We can use this language to synthetically build logical relations models [SH21]. In order to effectively construct such models, however, we must supplement type theory with primitives specific to $\mathbf{Gl}(\rho)$. The most fundamental of these is a proposition:

Definition 4.4. The syntactic proposition $\mathbf{syn} : \Omega$ is interpreted in $\mathbf{Gl}(\rho)$ as the subterminal object $(\mathbf{1}_{\mathcal{E}}, \mathbf{0}_{\mathcal{F}}, !)$.

Recalling the correspondence between objects of $\mathbf{Gl}(\rho)$ and predicates, $\mathbf{syn}$ is the predicate on $\mathbf{1}_{\mathcal{E}}$ with no computable elements. What makes this proposition useful is its ability to wipe out the obligation to track computable elements. A morphism $f : \mathbf{syn} \times A \longrightarrow B$ must contain a morphism $\pi_0(f) : \pi_0(\mathbf{syn} \times A) \cong \pi_0(A) \longrightarrow \pi_0(B)$, but there are no computable elements of $\mathbf{syn} \times A$ so $\pi_0(f)$ entirely determines $f$; there is a bijection $[\mathbf{syn} \times A, B]_{\mathbf{Gl}(\rho)} \cong [\pi_0(A), \pi_0(B)]_{\mathcal{E}}$. Internally, hypothesizing $\mathbf{syn}$ collapses the category to $\mathcal{E}$:

Lemma 4.5. There is an equivalence $\mathcal{E} \simeq \mathbf{Gl}(\rho)/\mathbf{syn}$.

In topos-theoretic terms, $\mathcal{E}$ is an open subtopos of $\mathbf{Gl}(\rho)$. As an open subtopos, we can present $\mathcal{E}$ internally to $\mathbf{Gl}(\rho)$ through a lex idempotent monad $\bigcirc A = \mathbf{syn} \to A$ [RSS20]. This modality has a strongly disjoint lex idempotent modality, $\bullet A$ [RSS20, Section 3.4]. While we could work with $\bullet$ entirely through this characterization, it is helpful to fix a