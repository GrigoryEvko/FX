92

Introduction

universe, which we will call UA I ∈ Path(U, Int, Int). By case analysis, we can use this path to define a function Code ∈ Circle → U as follows.

$$\text{Code } c := \left[ \begin{array}{l} \text{case } c \text{ of} \\ | \text{base} \mapsto \text{Int} \\ | \text{loop}(x) \mapsto \text{UA } I x \end{array} \right]$$

That is, we draw a picture of a circle in U by choosing the type Int as our point and UA I as our loop at that point. The transformation of the data (Int, I) into a function Circle → U, instrumented by the circle eliminator, is the aforementioned descent.

Now suppose we have an arbitrary path p ∈ Path(Circle, base, base). By applying Code to this path pointwise, we obtain a path λᵢᵀx. Code (p x) ∈ Path(U, Int, Int). We define our candidate integer corresponding to p by coercing 0 ∈ Int along this path.

$$\text{encode } p := \text{coe}_{x.\text{Code}(p x)}^{0 \to 1}(0) \in \text{Int}$$

This gives us an integer; is it the integer we want? If we apply encode to the constant path, we have a coercion along a constant path, which we can show corresponds to the identity function. (We henceforth use ∼ as an informal infix notation for paths.)

$$\text{encode } (\lambda_i^T x.\text{ base}) = \text{coe}_{x.\text{Int}}^{0 \to 1}(0) \rightsquigarrow 0 \in \text{Int}$$

On the other hand, if we supply λᵢᵀx. loop(x), coercion on a path formed by univalence transforms into an application of the underlying isomorphism, which sends n to n + 1.

$$\text{encode } (\lambda_i^T x.\text{ loop}(x)) = \text{coe}_{x.\text{UA } I x}^{0 \to 1}(0) \rightsquigarrow 0 + 1 = 1 \in \text{Int}$$

So encode does, at least, distinguish between the constant and single loop paths. Although we cannot inspect its behavior further without getting into the nature of composition and inversion of paths, suffice to say that we indeed have encode (λᵢᵀx. loopⁿ(x)) ∼ n ∈ Int for every integer n, where loopⁿ is an n-fold composition of the loop constructor.

By the same technique, we can extract witnesses from paths in our example of a quotient from Chapter 1, the integers modulo n. Recall that we wanted Intₙ to be the quotient of Int by the following relation.

$$m_0 \approx m_1 := (p : \text{Int}) \times \text{Id}(\text{Int}, m_1 - m_0, p \cdot n)$$

We can write a definition of Intₙ as a higher inductive type as follows.

n : Nat ≫ inductive Intₙ where

| int(m : Int) ∈ Intₙ

| mod(m : Int, x : I) ∈ Intₙ [x ≡ 0 ⇔ int(m) | x ≡ 1 ⇔ int(m + n)]