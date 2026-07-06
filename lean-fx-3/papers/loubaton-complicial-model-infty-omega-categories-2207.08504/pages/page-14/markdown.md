CHAPTER 1. (0,ω)-CATEGORIES AND PRESHEAVES ON Θ

Remark furthermore that the ω-category D_n represents n-cells, in the sense that Hom(D_n, C) ≅ C_n. We will not make the difference between n-cells and the corresponding morphism D_n → C.

Definition 1.1.1.4. The ω-category ∂D_n is obtained from D_n by removing the n-cell e_n. We thus have a morphism

$$i_n : \partial\mathbf{D}_n \to \mathbf{D}_n.$$

Note that ∂D_0 = ∅.

Definition 1.1.1.5. We say that an (0,ω)-category X is a polygraph if it can be constructed from the empty (0,ω)-category by freely adding arrows with specified source and target. That is if X can be obtained as a transfinite composition ∅ = X_0 → X_1 → ⋯ → X_i → colim X_i = X where for each i, the map X_i → X_{i+1} is a pushout of Π_S ∂D_n → Π_S D_{n+1}.

An arrow of a polygraph is said to be a generator if it is one of the arrows that has been freely added at some stage.

Each cell in a polygraph can be written as a composite of generators or iterated unit of generators (not necessarily in a unique way). For a n-cell f, the set of generators of dimension n that appear in such an expression (and even the number of times they appear) is the same for all such expressions. As a consequence, a composition of non trivial cells is always non trivial.

Definition 1.1.1.6. For any subset S of N*, we define the functor (_)^S : ω-cat → ω-cat sending a ω-category C to the category C^S such that for any n, there is an isomorphism C_n → C_n^S that sends every n-cell f to a cell f̅ fulfilling

$$\pi_{n-1}^-(\overline{f}) = \overline{\pi_{n-1}^+(f)} \quad \pi_{n-1}^+(\overline{f}) = \overline{\pi_{n-1}^-(f)}$$

if i ∈ S and

$$\pi_{n-1}^-(\overline{f}) = \overline{\pi_{n-1}^-(f)} \quad \pi_{n-1}^+(\overline{f}) = \overline{\pi_{n-1}^+(f)}$$

if i ∉ S. These functors are called dualities as they are inverse of themselves. Even if there are plenty of them, we will be interested in only a few of them. In particular, we have the odd duality (_)^{op}, corresponding to the set of odd integers, the even duality (_)^{co}, corresponding to the set of non negative even integers and the full duality (_)^o, corresponding to the set of all non negative integers. Eventually, we have equivalences

$$((_)^{co})^{op} \sim (_)^o \sim ((_)^{op})^{co}.$$

Definition 1.1.1.7. Let Psh(G)_{*,* be the category of globular set with two distinguished points, i.e. of triples (X, a, b) where a and b are elements of X_0. Let [_, 1] : G → Psh(G)_{*,* be the functor sending D_n on (D_{n+1}, {0}, {1}) and i_n^e on i_{n+1}^e. This induces by left Kan extension a functor [_, 1] : Psh(G) → Psh(G)_{*,* that we call the suspension. We leave it to the reader to check that whenever C has a structure of ω-category, [C, 1] inherits one from it. This functor then induces a functor

$$[\_, 1] : \omega\text{-cat} \to \omega\text{-cat}$$

that we calls again the suspension. Eventually, we denote by i_0^- : {0} → [C, 1] (resp. i_0^+ : {1} → [C, 1]) the morphism corresponding to the left point (resp. to the right point). For an integer n, we define by induction the functor Σ^n : Psh(G) → Psh(G) with the formula:

$$\Sigma^0 := id \quad \Sigma^{n+1} := \Sigma^n[\_, 1].$$

14