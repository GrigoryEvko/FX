allows us to prove a conclusion if we have already assumed it in the context.

This rule does not immediately adapt to our multimodal system. There is a sense in which modal reasoning is largely about the *control of assumptions*. The rôle of modalities very often seems to amount to a specification of who or which state of the world ‘owns’ an assumption, and when we should be able to use it. In this particular setting, the logical power of an assumption is attenuated by the presence of a lock operator $-,\widehat{\mathbf{\Omega}}_{\mu}$. The lock stops us from using the assumptions that it guards—unless there is a transformation that explicitly allows it.

There are three principles that determine the behaviour of locks.

**Principle 1.** A $\mu$-variable can escape the hold of a $\mu$-lock.

In symbols, this implies that the variable rule at the very least admits the inference

$$\overline{\Gamma, (\mu \mid \varphi), \widehat{\mathbf{\Omega}}_{\mu} \vdash \varphi @ n}$$

where for $\mu : n \rightarrow m$ the formation of the context presupposes that

$$\Gamma \text{ ctx } @ m \quad \varphi \text{ wff } @ n$$

If we view a lock $\widehat{\mathbf{\Omega}}_{\mu}$ as a protector of variables, we see that it acts as a $\mu$-firewall that only authorises $\mu$-assumptions to escape its hold. In another interpretation, the appearance of a lock at the end of a context signifies that we are currently reasoning in a $\mu$-protected environment, so we are entitled to access $\mu$-classified information.

As we have quotiented our contexts up to Eqs. (1) and (2), this ability of a $\mu$-assumption to escape a $\mu$-lock should be retained even when the locks match only up to composition. For example, given $\nu : o \rightarrow n$ and $\varphi \text{ wff } @ o$ we should also be able to use the variable rule to infer

$$\overline{\Gamma, (\mu \circ \nu \mid \varphi), \widehat{\mathbf{\Omega}}_{\mu}, \widehat{\mathbf{\Omega}}_{\nu} \vdash \varphi @ o}$$

precisely because $\Gamma, (\mu \circ \nu \mid \varphi), \widehat{\mathbf{\Omega}}_{\mu}, \widehat{\mathbf{\Omega}}_{\nu} = \Gamma, (\mu \circ \nu \mid \varphi), \widehat{\mathbf{\Omega}}_{\mu \circ \nu} @ o$.

The second principle allows us to weaken the requirement for an exact match between the modality and the lock:

**Principle 2.** The transformations of $\mathcal{M}$ are ‘keys’ for the lock.

In other words, suppose that for modalities $\mu, \nu : n \rightarrow m$ we have a transformation

$$\alpha : \nu \Rightarrow \mu$$

in $\mathcal{M}$. If we interpret this to mean that the modality $\nu$ implies (or is stronger than) the modality $\mu$, then intuition has it that $\nu$-modal assumptions should be able to ‘unlock’ a $\mu$-lock. In symbols:

$$\frac{\alpha : \nu \Rightarrow \mu}{\Gamma, (\nu \mid \varphi), \widehat{\mathbf{\Omega}}_{\mu} \vdash \varphi @ n}$$

The final principle is already well-known:

11