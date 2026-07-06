93

This is a bit different from the naive quotient Int // ≈: to avoid introducing redundant higher structure, we only construct paths m ∼ m + n, not paths m ∼ m + p · n for all p : Int. The latter are instead obtained by interated composition of the mod constructor: m ∼ m + 1 · n ∼ ⋯ ∼ m + (p - 1) · n ∼ m + p · n.

For any m₀, m₁ ∈ Int, we have an isomorphism I m₀ m₁ ∈ (m₀ ≈ m₁) ≃ (m₀ ≈ m₁ + n): if m₀ and m₁ differ by a multiple of n, then so do m₀ and m₁ + n, and vice versa. Using this, we can define a type family Code ∈ Int → Intₙ → U that takes m₀ and int(m₁) to m₀ ≈ m₁ by case analysis.

$$\text{Code } m_0 t_1 := \begin{bmatrix} \text{case } t_1 \text{ of} \\ | \text{int}(m_1) \mapsto m_0 \approx m_1 \\ | \text{mod}(m_1, x) \mapsto \text{UA}(I m_0 m_1) x \end{bmatrix}$$

Now, given any path p ∈ Path(Int, int(m₀), int(m₁)), we can extract a proof of m₀ ≈ m₁ by coercing the element ⟨0, P⟩ ∈ m₀ ≈ m₀ (where P is some proof that m₀ - m₀ ∼ 0 · n) along the line of types obtained by applying Code m₀ to p pointwise.

$$\text{encode } p := \text{coe}_{x.\text{Code } m_0 (p \times)}^0(\langle 0, P \rangle) \in m_0 \approx m_1$$

So we have encode ∈ Path(Int, int(m₀), int(m₁)) → m₀ ≈ m₁. With a bit more coding, we can show that encode is even an isomorphism; Intₙ is an effective quotient of Int by - ≈ -.

The computational content of paths is essential to this argument: Code examines the content of path constructors to convert them into univalence-wrapped isomorphisms, and coercion in turn inspects its input type line to extract an isomorphism and apply it.

**Outline** In the following chapters, we realize the promise of higher inductive types sketched above, defining a class of specifications that include such types as Intₙ and ||A|| and explaining each such specification as a computational object in a cubical type theory.

In Chapter 5, we begin by considering a number of representative examples of higher inductive types in more detail, exploring in particular how to implement coercion for each. In addition to proper higher inductive types, we also consider indexed inductive types; implementing coercion for these requires similar techniques despite the absence of explicit higher structure.

Chapter 6 is the meat of this part: we define a schema for specifying indexed higher inductive types, show that we can construct type systems closed under these types, prove that they support coercion and composition, and formulate and prove their introduction and elimination principles.

We close with a discussion of related and future work in Chapter 7.