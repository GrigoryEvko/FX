2. $X^n \equiv \Theta^{\partial \lambda_{\langle n \rangle}} \to \text{Type}_\ell$.
3. $h_n \equiv B^{(0)}$.
4. $t_n \equiv \gamma^{q_n}$.

We have already remarked that 1 and 3 are easy, and the base cases of 2 and 4 are likewise trivial. For the induction step of 2, we have

$$\begin{aligned} X^{n+1}[\partial x, x] &\equiv \{b : \text{EI}(h_{n-1} \partial x)\} \to (X^n)^d \langle \partial x, t_n \partial x \times b \rangle x \\ &\equiv \{b : B^{(0)} \partial x\} \to \Theta^{\partial \lambda_{\langle 1, \langle n \rangle \rangle}} \langle \partial x, t_n \partial x \times b \rangle x \to \text{Type}_\ell \\ &\equiv \Theta^{\partial \lambda_{\langle 1, \langle n \rangle \rangle}} [\gamma^{q_n}] \to \text{Type}_\ell \\ &\equiv \Theta^{\partial \lambda_{\langle 1, \langle n+1 \rangle \rangle}} [\partial x, x] \to \text{Type}_\ell. \end{aligned}$$

Finally, the induction step of 4 follows immediately from the definition of $\gamma^p$ and the inductive hypothesis of 2. This completes the proof of the correctness of our construction of semi-simplicial types.

## 5 Conclusion and Future Work

In this paper we have made two main contributions. First, we have described *Displayed Type Theory (dTT)*, a new kind of type theory that incorporates (unary) internal parametricity but guarded by a modality, and showed that any model of dependent type theory with countable Reedy limits can be lifted to a model of dTT using augmented semi-simplicial diagrams. Because the latter are diagrams on an *inverse* category, their type theory is more closely related to that of the original model, and indeed the original model sits inside our model of dTT at the discrete mode. In particular, unlike other internally parametric type theories, dTT is compatible with classical axioms such as excluded middle and choice, as long as they are formulated at the discrete mode (or under the modality $\diamond$), and can be used as an internal logic to reason about arbitrary $(\infty, 1)$-toposes.

Secondly, inside dTT we have introduced a notion of *displayed coinductive type*, where the output of a destructor can be a parametricity 'computability witness' of the input, and showed that as a particular case of this notion we can define a type of *semi-simplicial types*. This yields a new approach to the long-standing open problem of representing infinitely coherent higher structures in type theory. Relative to other approaches, ours has the advantage that semi-simplicial types are defined (not postulated) as a simple instance of a type-former with natural introduction and elimination rules, i.e. a categorical universal property. While it remains to be seen how much can actually be done in practice with our definition, early indications of its utility are promising.

There are a number of directions for future work suggested by our results; here we survey a few of them briefly.

**5.0.0.1 Computation and implementation.** We conjecture that dTT satisfies canonicity and normalization, and should therefore be possible to implement in a proof assistant.

97