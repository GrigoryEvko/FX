**Example 3.4** *The (contravariant) pullback pseudo-functor $\mathbb{LOC}(X) = \mathbf{Loc}/X$ is a stack, essentially by definition of effective descent morphism. Let $f: Y \longrightarrow X$ be a locale map. The definition of $f^*$ being monadic is that the canonical functor $f^*: \mathbf{Loc}/X \longrightarrow (\mathbf{Loc}/Y)^{\mathbb{T}_f}$ is an equivalence, where $\mathbb{T}_f$ is the monad on $\mathbf{Loc}/Y$ determined by the pullback adjunction $\Sigma_f \dashv f^*$. But the algebras of $\mathbb{T}_f$ are exactly the $\mathbb{Y}_f$-objects for the internal groupoid $\mathbb{Y}_f$ which we have already seen can be identified with $Des(\mathbb{LOC}, f)$.*

**Example 3.5** *Given $\mathbb{G}$ a localic groupoid, then the contravariant pseudo-functor $X \mapsto \text{Prin}_{\mathbb{G}}(X)$ is a stack. This is proved for example in [B90] (Theorem 4.11) in the case where the notion of cover used is that of an open surjection; but a proof using effective descent morphism instead is exactly the same.*

The identification of $\mathbf{Loc}/X$ with $Des(\mathbb{LOC}, f)$ for $f$ an effective descent morphism also allows for a short proof that open and proper maps descend:

**Proposition 3.6** *Given a localic effective descent morphism $f: Y \longrightarrow X$, if $g: A_a \longrightarrow B_b$ is a locale map over $X$ such that $f^*(g)$ is open (resp. proper) over $Y$ then $g$ is open (resp. proper).*

*Proof:* By change of base, since the pullback of $f$ along $b: B \longrightarrow X$ is still an effective descent morphism, we can assume that $B = X$ and are left checking that if $P_Y^L(f^*A)$ has a top element then so does $P_X^L(A_a)$. But the pullbacks of the top element $\top: 1 \longrightarrow P_Y^L(f^*A_a)$ along both $\pi_1: Y \times_X Y \longrightarrow Y$ and $\pi_2: Y \times_X Y \longrightarrow Y$ are again top elements (recall that $\mathbf{Loc}$ is order enriched cartesian; that is, pullback preserves the order enrichment). Both pullbacks must therefore be the same by uniqueness of top elements. Therefore $\top$ is a morphism of $Des(\mathbb{LOC}, f)$ and corresponds to a top element for $P_X^L(A_a)$ via $\mathbf{Loc}/X \simeq Des(\mathbb{LOC}, f)$.

The conclusion for proper maps is order dual. $\square$

**Example 3.7** *For any locale $X$ let $\mathbf{KHLoc}_X$ be the full subcategory of $\mathbf{Loc}_{Sh(X)}$ consisting of compact Hausdorff locales. As pullback preserves proper maps the assignment $X \mapsto \mathbf{KHLoc}_X$ (and morphisms mapping to pullback) is a pseudo-functor $\mathbf{Loc}^{op} \longrightarrow \mathfrak{CAT}$ which is a sub-pseudo-functor of the previous example in an obvious manner. To prove that it is a stack, we just need to check that proper maps descend along effective descent morphisms; this has been covered in the previous proposition.*

**Example 3.8** *The pseudo-functor $X \mapsto Sh(X)$ is a stack. This follows as in the previous example, but with open maps in place of proper maps; recall that for any locale $X$, $Sh(X) \simeq \mathbf{LH}/X \simeq \mathbf{Dis}_X$. That is, the category of sheaves over $X$ is equivalent to the category of discrete locales internal to the topos $Sh(X)$.*

Any stack $M: \mathbf{Loc}^{op} \longrightarrow \mathfrak{CAT}$ gives rise to a stack of groupoids; consider $X \mapsto M^{\cong}(X)$ where $M^{\cong}(X)$ has the same objects as $M(X)$, but has as morphisms only those morphisms of $M(X)$ that are isomorphisms. Proving this requires the simple verification that all the functors involved in the relevant definitions preserve isomorphisms.

5