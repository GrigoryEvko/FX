Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:3

proof of correctness typically proceeds by establishing properties (1)-(3) in order. Each property, moreover, requires a separate argument. Completeness is established through a PER model, soundness through a cross-language logical relation, and idempotence through a final inductive argument. The first two properties in particular are time-consuming to verify; recent work by Gratzer et al. [GSB19a] extended NbE to a type theory with an idempotent comonad but even in this minimal case the correctness proof occupied a 90 page technical report [GSB19b].

These difficulties are not unique to modal type theories, and a long line of research focuses on taming the complexity of NbE through gluing [AHS95, Str98, Fio02, AK16, Coq19, Ste21]. This line of work recasts normalization algorithms as the construction of models of type theory in categories defined by Artin gluing.

1.3. Normalization-by-gluing. Stepping back from type theory and normalization, fix a functor $F : \mathcal{C} \longrightarrow \mathcal{D}$ between a pair of categories. The gluing of $F$ (written $\mathbf{Gl}(F)$) is a category whose objects triples $(C : \mathcal{C}, D : \mathcal{D}, f : D \longrightarrow F(C))$. Morphisms in this category are given by pairs of morphisms $(x_0, x_1)$ fitting into a commuting square, e.g.:

$$\begin{array}{c} D_0 \xrightarrow{x_1} D_1 \\ f_0 \Bigg\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ F(C_0) \xrightarrow{F(x_0)} F(C_1) \end{array}$$

We note that there are evident projection functors $\pi_0 : \mathbf{Gl}(F) \longrightarrow \mathcal{C}$ and $\pi_1 : \mathbf{Gl}(F) \longrightarrow \mathcal{D}$.

We will view $\mathbf{Gl}(F)$ as a category of proof-relevant predicates on $\mathcal{C}$. To illustrate this, consider $\mathcal{E} = \mathbf{Gl}(\Gamma)$ where $\Gamma = [\mathbf{1}, -] : \mathcal{C} \longrightarrow \mathbf{Set}$ is the global sections map on a cartesian closed category $\mathcal{C}$ sending each object to the set of its global points. Objects in $\mathcal{E}$ then correspond to an object $C : \mathcal{C}$ equipped with a map of sets $\pi : X \longrightarrow [\mathbf{1}, C]$. Shifting perspective, we can view $\pi$ as a (proof-relevant) predicate on the global points of $C$ by setting $\Phi(c) = \pi^{-1}(c)$.

Remarkably, $\mathcal{E}$ inherits much of the structure of $\mathcal{C}$ so that $\mathcal{E}$ is also a Cartesian closed category and $\pi_0$ preserves finite products and exponentials. This is a recurrent pattern with Artin gluing; if $F : \mathcal{C} \longrightarrow \mathcal{D}$ is a nice functor between categories closed under (co)limits, exponentials, etc., then $\mathbf{Gl}(F)$ will be closed under the same operations in such a way that $\pi_0$ preserves them. In fact, unfolding the construction of e.g. binary products and exponentials in $\mathcal{E}$ yields the definition familiar from logical relations.

Example 1.2. Viewing objects of $\mathcal{E}$ as proof-relevant predicates as described above, the exponential $(C, \Phi)^{(D,\Psi)}$ is given by the following pair $(C^D, \Xi)$ where $\Xi$ is defined as follows (writing $\epsilon$ for the evaluation map associated with $C^D$):

$$\Xi(f) = \prod_{d \in [\mathbf{1}, D]} \Psi(d) \to \Phi(\epsilon \langle f, d \rangle)$$

Informally, therefore, we view $\mathbf{Gl}(F : \mathcal{C} \longrightarrow \mathcal{D})$ as the category of $\mathcal{D}$-valued predicates on $\mathcal{C}$ and the construction of exponentials, products, etc. within $\mathbf{Gl}(F)$ corresponds to defining a logical relation on $\mathcal{C}$. See Mitchell and Scedrov [MS93] for an exposition on this perspective.