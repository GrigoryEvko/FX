# **Principle 3.** The variable rule should be stable under weakening.

The idea here is that weakening should be admissible independently of the position of locks: if we have an inference in context $\Gamma, \widehat{\bullet}_\mu$ we should also be to admit it in either $\Gamma, (\nu \mid \varphi), \widehat{\bullet}_\mu$ or $\Gamma, \widehat{\bullet}_\mu, (\nu' \mid \varphi)$ for appropriately-typed modalities $\nu$ and $\nu'$. Moreover, this should only apply to tagged assumptions: introducing a new lock should by no means be admissible! That is, if we have an inference in context $\Gamma$, it should not in general be possible to also have it in $\Gamma, \widehat{\bullet}_\mu$, as $\widehat{\bullet}_\mu$ might protect some of the assumptions in $\Gamma$ by prohibiting their use.

Combining those three principles we see that the assumption rule should more or less function in the following manner:

1. It should gather all the locks to the right of the relevant assumption.
2. It should compose the modalities associated with each one of these locks.
3. It should allow the use of an assumption whenever its tag is stronger than the locks that protect it, i.e. the locks to its right.

In symbols we write

$$\frac{\mu : n \rightarrow m \quad \alpha : \mu \Rightarrow \text{locks}(\Delta)}{\Gamma, (\mu \mid A), \Delta \vdash A @ m}$$

where the function $\text{locks}(-)$ is defined by the following inductive clauses:

$$\begin{aligned} \text{locks}(\cdot) &\stackrel{\text{def}}{=} 1 \\ \text{locks}(\Gamma, (\mu \mid A)) &\stackrel{\text{def}}{=} \text{locks}(\Gamma) \\ \text{locks}(\Gamma, \widehat{\bullet}_\mu) &\stackrel{\text{def}}{=} \text{locks}(\Gamma) \circ \mu \end{aligned}$$

It is evident that this function is well-defined on contexts, for it respects Eqs. (1) and (2).

**Locks vs. modalities** The modal rules of the system reveal the close interaction between locks and modal operators.

Broadly speaking, the lock operators $-, \widehat{\bullet}_\mu$ are used to 'filter' the assumptions in the context, keeping only those that are allowed in a proof of a formula under the modality $\langle \mu \mid - \rangle$. This is encoded in the introduction rule, viz.

$$\frac{\mu : n \rightarrow m \quad \Gamma, \widehat{\bullet}_\mu \vdash \varphi @ n}{\Gamma \vdash \langle \mu \mid \varphi \rangle @ m}$$

which allows us to prove the modal formula $\langle \mu \mid \varphi \rangle$ from the context $\Gamma$ exactly whenever we can prove $\varphi$ from a $\mu$-locked $\Gamma$. Thus, when trying to prove $\langle \mu \mid \varphi \rangle$ it suffices to prove $\varphi$, but with restrictions on the proof. More precisely, we are able to use only those assumptions whose modal tag is at least as strong as $\mu$.

12