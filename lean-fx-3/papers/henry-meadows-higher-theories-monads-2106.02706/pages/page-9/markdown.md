so $U_{x,y} \circ V_{x,y}$ is the composition by an equivalence by our assumptions, hence $U_{x,y} \circ V_{x,y}$ is an equivalence. Similarly, we have that $V_{x,y} \circ U_{x,y} \simeq \epsilon_y \circ F(G(-) \circ \eta_x) = \epsilon_y \circ FG(-) \circ F(\eta_x) \simeq (-) \circ \epsilon_{Gx} \circ F(\eta_x)$, so $V_{x,y} \circ U_{x,y}$ is also an equivalence. It hence follows that $U_{x,y}$ and $V_{x,y}$ are both equivalences. $\square$

In Section 5, we show that the monad-theory correspondence is an *idempotent adjunction*. We will exploit the idempotence of the adjunction throughout the paper, especially in Section 8. Thus, we will review the definition and basic properties of idempotent adjunctions below:

**Lemma 2.3.** *Suppose that $L \dashv R$ is an adjunction with counit $\epsilon$ and unit $\eta$. Then one of the following natural transformations $(\epsilon)L, R(\epsilon), \eta(R), L(\eta)$ is an equivalence if and only if each of them are equivalences. If any (and hence all) of the above natural transformations are equivalences, we say that the adjunction is idempotent.*

*Proof.* The classical, or 1-categorical, analogue of this fact is [17, Proposition 2.8]. The proof given there carries forward to the $\infty$-categorical case, either because it is essentially an excercise in manipulating the counit-unit identities, or be applying the 1-categorical result to the homotopy category and the adjunction between the derived functors of $L$ and $R$. $\square$

*Remark 2.4.* A useful fact about idempotent adjunctions is that the restrict to an equivalence $im(R) \simeq im(L)$ between the essential images of $R$ and $L$, essentially by definition. It is also important to note that if $X \in im(L), Y \in im(R)$, then also by definition $LRX \simeq X, Y \simeq RLY$.

*Remark 2.5.* Given an adjunction $L \dashv R$, written $L : \mathcal{C} \leftrightarrows \mathcal{D} : R$, post-composition with $L$ and $R$ induces an adjunction:

$$(L \circ -) : \text{Fun}(\mathcal{T}, \mathcal{C}) \leftrightarrows \text{Fun}(\mathcal{T}, \mathcal{C}) : (R \circ -)$$

for any $\infty$-category $\mathcal{T}$. A natural transformation $LX \rightarrow Y$ corresponds to a natural transformation $X \rightarrow RY$ simply by functoriality of the correspondence between arrows $L(a) \rightarrow b$ and arrows $a \rightarrow R(b)$.

But on the other hand, pre-composition with $L$ and $R$ induces an adjunction in the other direction:

$$(- \circ R) : \text{Fun}(\mathcal{D}, \mathcal{T}) \leftrightarrows \text{Fun}(\mathcal{T}, \mathcal{C}) : (- \circ L)$$

9