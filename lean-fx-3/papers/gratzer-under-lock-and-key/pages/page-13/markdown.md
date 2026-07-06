The modal elimination rule

$$\frac{\nu : o \rightarrow n \quad \mu : n \rightarrow m \quad \Gamma, \widehat{\bullet}_\mu \vdash \langle \nu \mid \varphi \rangle @ n \quad \Gamma, (\mu \circ \nu \mid \varphi) \vdash \psi @ m}{\Gamma \vdash \psi @ m}$$

is the most complicated rule of the system. Its *major premise* (i.e. the premise whose connective is being eliminated) is $\Gamma, \widehat{\bullet}_\mu \vdash \langle \nu \mid \varphi \rangle @ n$. Notice that this judgement could be turned into $\Gamma \vdash \langle \mu \mid \langle \nu \mid \varphi \rangle \rangle @ m$ by applying the introduction rule. Putting the transformed major premise and the minor premise side-by-side

$$\Gamma \vdash \langle \mu \mid \langle \nu \mid \varphi \rangle \rangle @ m \quad \Gamma, (\mu \circ \nu \mid \varphi) \vdash \psi @ m$$

we see that this elimination rule is almost a cut rule! This is particularly evident if we recall that $\langle \mu \mid \langle \nu \mid \varphi \rangle \rangle$ is supposed to be logically equivalent to $\langle \mu \circ \nu \mid \varphi \rangle$, which is also supposed to be equivalent to the tagged assumption $(\mu \circ \nu \mid \varphi)$.

Despite appearances, this elimination rule is subtle: it allows the prover to ‘split’ a composite modality $\mu \circ \nu$ into its constituent parts, keeping the second half $\mu$ as a lock in the context of the major premise, and eliminating only the first half $\nu$. In fact, we will see in §4 that the modal elimination rule is the central device that allows highly non-trivial interactions between modalities to appear as reasoning principles in the logic.

**Implication** As is usual in natural deduction, the implication introduction rule

$$\frac{\Gamma, (\mu \mid \varphi) \vdash \psi @ m}{\Gamma \vdash (\mu \mid \varphi) \rightarrow \psi @ m}$$

internalises the usual deduction theorem as a rule of the proof system, by allowing the prover to discharge an assumption. This is exactly why the compound implication $(\mu \mid \varphi) \rightarrow \psi$ is a natural connective in this logic: its antecedent mirrors the structure of assumptions in the proof system.

The elimination rule is a form of *modal modus ponens*:

$$\frac{\mu : n \rightarrow m \quad \Gamma \vdash (\mu \mid \varphi) \rightarrow \psi @ m \quad \Gamma, \widehat{\bullet}_\mu \vdash \varphi @ n}{\Gamma \vdash \psi @ m}$$

If we can prove the implication $(\mu \mid \varphi) \rightarrow \psi$ then proving $\varphi$ in a $\mu$-locked context suffices to obtain $\psi$. Notice once more that the minor premise can be transformed into $\Gamma \vdash \langle \mu \mid \varphi \rangle @ m$ by one application of the modal introduction rule. Thus, if we consider the assumption $(\mu \mid \varphi)$ and the formula $\langle \mu \mid \varphi \rangle$ to be equivalent, this rule is simply modus ponens, but a little bit more accommodating towards the structure of locks.

### 3.5. Metatheory

The system satisfies a number of the usual metatheorems. First, one is able to show the admissibility of the usual structural rules of weakening and exchange. Some additional care is needed in the case of weakening to ensure that the weakened context is well-formed.

13