**Theorem 3.1** (Structural rules). *The following rules are admissible.*

$$\frac{\Gamma, (\mu \mid \varphi), \Delta \text{ ctx } @p \quad \Gamma, \Delta \vdash C @p}{\Gamma, (\mu \mid \varphi), \Delta \vdash C @p} \quad \frac{\Gamma, (\mu \mid \varphi), (\nu \mid \psi), \Delta \vdash C @p}{\Gamma, (\nu \mid \psi), (\mu \mid \varphi), \Delta \vdash C @p}$$

We cannot in general weaken a context by adding a lock. In fact, locks transport contexts between modes, so adding arbitrary locks to a context may well map a well-formed context $\Gamma \text{ ctx } @m$ to one that is not well-formed. However, we can 'weaken a $\mu$-lock' by replacing it with one corresponding to a $\nu$-lock for a 'weaker' $\nu$, i.e. a modality with the same boundary (source and target modes) for which there exists some $\alpha : \mu \Rightarrow \nu$.

**Theorem 3.2** (Lock Weakening). *The following rule is admissible.*

$$\frac{\Gamma, \text{🖼}_\mu, \Delta \vdash \varphi @p \quad \alpha : \mu \Rightarrow \nu}{\Gamma, \text{🖼}_\nu, \Delta \vdash \varphi @p}$$

Finally, we can prove that a modal version of the cut rule is admissible.

**Theorem 3.3** (Cut). *The following rule is admissible:*

$$\frac{\Gamma, \text{🖼}_\mu \vdash \varphi @n \quad \Gamma, (\mu \mid \varphi), \Delta \vdash \psi @b}{\Gamma, \Delta \vdash \psi @b}$$

These metatheorems will be shown as corollaries of theorems in §5.

#### 4. EXAMPLES

In this section we demonstrate modal reasoning using our proof system.

Recall that $\varphi \rightarrow \psi \stackrel{\text{def}}{=} (1 \mid \varphi) \rightarrow \psi$. The usual modus ponens is then a *derived* rule:

$$\frac{\Gamma \vdash \varphi \rightarrow \psi @m \quad \Gamma \vdash \varphi @m}{\Gamma \vdash \psi @m}$$

This follows from the elimination rule because by Eq. (1) we have $\Gamma, \text{🖼}_1 = \Gamma$.

**Some general theorems about modal formulas** We begin by showing some theorems that hold irrespective of the choice of mode theory. This determines the nature of our modalities—which are shown to automatically preserve conjunctions—and showcases the various rules in action.

First, we can show that a modal antecedent $(\mu \mid \varphi)$ implies its corresponding modal formula. For any $\mu : n \rightarrow m$ and $\varphi \text{ wff } @n$ we have

$$\frac{1_\mu : \mu \Rightarrow \mu}{\frac{(\mu \mid \varphi), \text{🖼}_\mu \vdash \varphi @n}{(\mu \mid \varphi) \vdash \langle \mu \mid \varphi \rangle @m}} \\ \hline \vdash (\mu \mid \varphi) \rightarrow \langle \mu \mid \varphi \rangle @m$$

14