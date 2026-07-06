Related work

219

|  This paper | [BCM15] | [Mou16]  |
| --- | --- | --- |
|  Bridge(x.A, a₀, a₁) | A ≃ₓ a | (∀x.A) ≃ a  |
|  λ¹(∥x]a | a · x | (⟨x⟩a)!  |
|  p x | (a,x p) | (⟨a,x p⟩)  |
|  extentₓ(-; a₀.t₀, a₁.t₁, a₀.a₁.ā.u) | ⟨λa.tₓ λa.λā.u⟩ | ⟨λa.tₓ λa.λā.u⟩  |
|  Gelₓ(A₀, A₁, a₀.a₁.R) | (a : A) ×ₓ R | A ≗ₓ R  |
|  gelₓ(a₀, a₁, c) | (a,x c) | (⟨a,x p⟩)  |
|  ungel(x.a) | a · x | (⟨x⟩a)!  |

Figure 12.1: Translation dictionary for internal parametricity

combinations of terms relating first interval dependency to rays and then rays to bridges. In particular, A ≗ₓ R is syntactic sugar for a term ⟨A, ΨₐR⟩@x, while ⟨f,ₓ h⟩ is sugar for ⟨f, Φf h⟩@x. As a result, equivalents of Gel and extent are sometimes called Ψ- and Φ-operators respectively in the literature.

**Internal parametricity à la Nuyts et al.** Nuyts, Vezzosi, and Devriese [NVD17] define a second internally parametric type theory building on Bernardy et al.'s work. Their system, **ParamDTT**, follows the BCM theory by employing intervals to express the action of terms on relations. Like our own theory, Nuyts et al.'s includes two kinds of interval, defining "bridges" and "paths", and our own use of the word "bridge" is borrowed from this word.

However, the coincidence of terminology is somewhat misleading. **ParamDTT**'s paths provide a much weaker notion of heterogeneous equality; paths are not in general required to satisfy anything like the Kan operations. The only requirement is that *homogeneous* paths give rise to identities, what Nuyts et al. call the *path degeneracy axiom*.

$$\frac{P \in \text{Path}(\dots A, M_0, M_1)}{\text{degax}(P) \in \text{Id}(A, M_0, M_1)}$$

**ParamDTT**'s paths are therefore closer in spirit to the heterogeneous equalities of Observational Type Theory [AMS07] than to those of cubical type theory. From our perspective, it may be more natural to think of these paths as more like a second, stronger form of bridge. Indeed, Nuyts and Devriese [ND18] have since developed a more general system that includes a tower of notions of *n-relatedness*, with **ParamDTT**'s paths and bridges as the first two levels. In order to avoid confusion with our own terminology, we henceforth