which states that knowledge implies belief. We could also add a *strong introspection* transformation, that states that an agent knows what they believe:

$$\text{Introspe} : B_i \Rightarrow K_i \circ B_i$$

Whether any coherence laws naturally arise in this setting is yet to be determined.

**A multimode logic** Our discussion would not be complete without including a bona fide *multimode* logic. To our knowledge no such logics have appeared before. However, in our work on multimodal Martin-Löf type theory we have found multimode settings extremely useful, especially when there are two distinct ‘universes of discourse’ that we are trying to model. The scenario usually involves a universe of discourse in which some particular principle holds (e.g. some axiom or induction principle), and another in which it does not. These are related by modalities, so that the formulas in one are available in the other under a modality, and can also be related to the formulas of another mode.

We wish illustrate that perspective in the simplest possible way. Consider the mode theory consisting of two objects, int and cl, and a single modality

$$\mathbf{P} : \text{int} \rightarrow \text{cl}$$

The idea is that the mode cl corresponds to classical logic, and the mode int corresponds to intuitionistic logic. In this setup we are able to add the excluded middle axiom to the rules of the classical mode:

$$\frac{\varphi \text{ wff @ cl}}{\Gamma \vdash \varphi \vee \neg \varphi @ \text{ cl}}$$

We do *not* include this rule in the logic of the intuitionistic mode int. If we can prove $\vdash \langle \mathbf{P} \mid \varphi \rangle @ \text{ cl}$ then we know that $\varphi$ is a theorem of intuitionistic propositional logic. Thus, only the theorems of intuitionistic logic are available under the modality $\mathbf{P}$.

Notice that this modality $\mathbf{P}$ is not really an ‘inclusion.’ For example, we are not able to prove $\langle \mathbf{P} \mid \varphi \rangle \rightarrow \varphi @ \text{ cl}$. In fact, this formula need not even be well-formed! To form $\langle \mathbf{P} \mid \varphi \rangle \text{ wff @ cl}$ we must have that $\varphi \text{ wff @ int}$, and concluding that $\varphi \text{ wff @ cl}$ from that assumption is a non-trivial metatheorem about the logic.

In the classical mode we may infer that

$$\frac{\varphi \text{ wff @ int}}{\Gamma \vdash \langle \mathbf{P} \mid \varphi \rangle \vee \neg \langle \mathbf{P} \mid \varphi \rangle @ \text{ cl}}$$

That is: in the classical mode we can infer that it is either true or false that $\varphi$ is intuitionistically provable. Thus, the classical mode of this logic can be seen as a place where one may reason about provability in intuitionistic logic!

## 5. A MULTIMODAL $\lambda$-CALCULUS

In this final section we establish a *Curry-Howard correspondence* [Gal93; GLT89; How80; SU06] for multimodal logic. This is traditionally achieved as follows. Beginning with a

19