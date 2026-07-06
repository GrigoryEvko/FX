Example 4.50. Recall that for semi-simplicial types SST, we have $\Phi \equiv ()$, with $A \equiv \text{Type}$ and $\mathcal{B} a \equiv \{x : \text{El } a\}$. Therefore, in this case we have

$$X^0 \equiv \text{Type}$$

$$X^0 A_0 \equiv \text{El } A_0 \to \text{Type}^d A_0$$

$$\equiv \text{El } A_0 \to \text{El } A_0 \to \text{Type}$$

$$X^2 A_0 A_1 \equiv (a_1 : A_0) \to \{(A \to A \to \text{Type})\}_{A : \text{Type}^d} A_0 (A_1 a_1) A_1$$

$$\equiv (a_1 : A_0) \to \{((x : A)(x' : A' x)(y : A)(y' : A' y) \to \text{Type}^d (A'' x y))\}$$

$$A : \text{Type}, A' : \text{Type}^d A, A'' : A \to A \to \text{Type} A_0 (A_1 a_1) A_1$$

$$\equiv (a_{01} : A_0)(a_{10} : A_0)(a_{01} : A_1 a_{01} a_{10})$$

$$(a_{10} : A_0)(a_{01} : A_1 a_{01} a_{10})(a_{10} : A_1 a_{10} a_{10}) \to \text{Type}$$

This suggests that in general, $X^{\partial n}$ will be the type of $(n-1)$-truncated semi-simplicial types, while $X^n A$ will be the type of ways to extend such an $A$ to an $n$-truncated one, i.e. the types of indexed families of $n$-simplices. We will prove this formally in section 4.5.5.

It remains to show that this construction of dCoind has the structure stipulated in section 3.3. To this end, we first unpack what it means for a type $C \in \text{Ty}(\Gamma \bullet_{\triangle\square} | \Phi)$ to be an $\overline{\text{F}}$-coalgebra. This means it is equipped with a section of the projection $\overline{\text{F}}(C) = (C | \text{F}(C)) \to C$, which syntactically is to say a partial substitution

$$\Gamma, \bullet_{\triangle\square} | (\phi : \Phi), x : C \vdash_{sm} c : (a : A \phi, x' : (b : \mathcal{B} \phi a) \to X^d \langle \phi, \sigma a b \rangle x).$$

But this is equivalent to giving its components, which we abstract over $x$ to emphasise their dependence on it:

$$\Gamma, \bullet_{\triangle\square} | (\phi : \Phi) \vdash_{sm} h : C \to A \phi$$

$$\Gamma, \bullet_{\triangle\square} | (\phi : \Phi) \vdash_{sm} t : (x : C)(b : \mathcal{B} \phi (h x)) \to X^d \langle \phi, \sigma (h x) b \rangle x$$

This is evidently precisely the structure of head and tail from section 3.3. Thus, our terminal $\overline{\text{F}}$-coalgebra admits these destructors.

Furthermore, to give some other telescope $\Theta \in \text{Tel}(\Gamma \bullet_{\triangle\square} | \Phi)$ an $\overline{\text{F}}$-coalgebra structure is equivalent to equipping $\Upsilon \equiv (\Phi | \Theta)$ with the premises of the corecursor, where the indices-assigning map $\zeta : (\Phi | \Theta) \to \Phi$ is the dependent projection. Thus, terminality of our terminal $\overline{\text{F}}$-coalgebra implies that it admits the corecursor for telescopes $\Upsilon$ of this form.

In the models arising from type-theoretic model toposes, the underlying category is actually locally cartesian closed, and thus the functor $\overline{\text{F}}$ can be extended from $\text{Tel} \not\parallel (\Gamma \bullet_{\triangle\square} \Phi)$ to the larger slice category $(\text{Tel} \not\parallel (\Gamma \bullet_{\triangle\square})) / \Phi$, with the same terminal coalgebra in this larger category. This directly implies the full corecursion principle, since $\zeta$ in that rule equips $\Upsilon$ with the structure of an object of this slice.

In fact, the same is true for arbitrary models: the premises of the corecursor equip $\Upsilon$ with 'enough of an $\overline{\text{F}}$-coalgebra structure' to deduce the existence of a unique compatible map to the terminal coalgebra. In the next section we prove this in a more general abstract context.

### 4.5.3 Terminal generalised coalgebras

Let $\text{F}$ be a copointed endofunctor of a category $\mathcal{C}$ as in section 4.5.1, where $\mathcal{C}$ is a full subcategory of some larger category $\text{E}$.

87