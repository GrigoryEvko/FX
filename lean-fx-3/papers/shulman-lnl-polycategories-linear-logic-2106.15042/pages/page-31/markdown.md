Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:31

universal, it can be $\pi$-extremal for the unique functor $\pi : \mathcal{P} \to \text{LNLMULTI}$ (see Remark 2.3). This yields the correct “modified” notion of initial and terminal object in an LNL multicategory as discussed in Section 2, since not all expansions of this cone factor through LNLMULTI. Since LNLMULTI is subterminal, Proposition 4.24 applies to LNL multicategories, so there is no ambiguity in the correct notion of “bicomplete LNL multicategory”.

Similarly, we obtain the correct notions of limit and colimit for symmetric polycategories, cartesian multicategories, symmetric multicategories, and CBPV pre-structures. The non-subterminals from Remarks 2.4 and 2.7 also satisfy the condition of Proposition 4.24, so there is no ambiguity in their correct notion of bicompleteness either.

The potential difference between relative and fiberwise bicompleteness can be attributed to the fact that Definitions 4.16 and 4.18 overlap. Specifically, the abstract cartesianness cone $\mathcal{C}art_{\Phi/K}$ when $\Phi$ is a single object of the same sort and opposite sign as $K$ coincides with an abstract limit or colimit cone where $\mathcal{A}$ is the terminal category. In the absolute case, this is a universal unary co-unary morphism between objects of the same sort, as in Remark 2.17, or equivalently a limit or colimit of a single object, which is trivial. But if $\pi : \mathcal{P} \to \mathcal{Q}$ has extremal lifts for these unary co-unary cones, then its underlying ordinary functors between categories of linear and nonlinear objects are each both a fibration and opfibration, in the classical Grothendieck sense.

**Example 4.26.** The non-subterminal $\mathcal{Q} = \text{SMADJ}$ from Example 4.8 contains a nonidentity morphism $\mathcal{P} \to \mathbb{N}$ between linear objects. Thus, while a fiberwise bicomplete object of LNLPoly/SMADJ contains only limits and colimits of positive and negative objects individually, a relatively bicomplete one also includes the cartesian lifts mentioned in Example 4.8 that make it an adjunction of symmetric multicategories.

Since these adjoint functors relating positive and negative objects are analogous to the exponential modalities relating linear and nonlinear objects, and do not intuitively look like a sort of “limit”, it is natural to view them as belonging to birepresentability and *not* to “completeness”. As pointed out by the referee, this argues for fiberwise bicompleteness as the correct notion of “bicompleteness” for general base objects $\mathcal{Q}$.

Our general notion of “extremal cone” also includes examples that don’t fall into either Definition 4.16 or Definition 4.18. However, our main purpose in introducing it is to give a common language to talk about these two examples. To this end, we note that together these two examples suffice to reconstruct all extremal cones.

**Theorem 4.27.** *For any functor $\pi : \mathcal{P} \to \mathcal{Q}$ of LNL polycategories, the following are equivalent.*

- (i) $\mathcal{P}$ has an extremal lift of any concrete cone $H : \mathcal{C} \to \mathcal{Q}$ (with $\mathcal{C}$ small).
- (ii) $\mathcal{P}$ is a relatively bicomplete bifibration.
- (iii) $\mathcal{P}$ is a fiberwise bicomplete bifibration.

*Proof.* Example 4.21 and Definition 4.22 show that (i)$\Rightarrow$(ii), and clearly (ii)$\Rightarrow$(iii). So let us assume (iii), and let $H : \mathcal{C} \to \mathcal{Q}$ be a cone and $G : \partial\mathcal{C} \to \mathcal{P}$ a lift of its reduct to $\mathcal{P}$. For any abstract projection $f \in \mathcal{C}(\Phi, K)$, let $\tilde{f} \in \mathcal{P}(G\Phi, K_f)$ be $\pi$-extremal in $K_f$ and such that $\pi(\tilde{f}) = H(f)$ and hence $\pi(K_f) = H(K)$, where the sign and linearity of $K_f$ are the same as that of $K$. Such a morphism exists because $\pi$ is a bifibration.

Now for any abstract transition $g \in \mathcal{C}(\Psi, L)$ and any abstract projection $f \in \mathcal{C}(L^\bullet, \Phi, K)$ that it is composable with, producing an abstract projection $f \circ_L g \in \mathcal{C}(\Psi, \Phi, K)$, the