We write $\mathbf{W}$ for the class of maps in $\mathfrak{SE}$ whose canonical cofibrant replacement is in $\mathbf{W}_{\mathrm{cof}}$. This is the class of weak equivalences of the effective model structure, to be established in Theorem 9.9.

**Lemma 9.7.** *Let $A \to B$ in $\mathfrak{SE}$. Then, the following are equivalent:*

(i) the map $A \to B$ is in $\mathbf{W}$,
(ii) the map $A \to B$ has a cofibrant replacement in $\mathbf{W}_{\mathrm{cof}}$,
(iii) all cofibrant replacements of the map $A \to B$ are in $\mathbf{W}_{\mathrm{cof}}$.

*Proof.* This is a standard argument, dual to the one of Lemma 9.3. What is used is closure properties of trivial fibrations (part (ii) of Lemma 1.5) and the model structure on $\mathcal{E}_{\mathrm{cof}}$ of Proposition 9.6. $\square$

**Corollary 9.8.** *The class $\mathbf{W}$ satisfies the 2-out-of-3 property.*

*Proof.* This is analogous to the proof of Corollary 9.4. $\square$

We can finally establish the existence of the effective model structure on $\mathfrak{SE}$.

**Theorem 9.9** (The effective model structure). *Let $\mathcal{E}$ be a countably lextensive category.*

(i) The category $\mathfrak{SE}$ of simplicial objects in $\mathcal{E}$ admits a model structure determined by the two weak factorisation systems of Theorem 4.2.
(ii) A map between fibrant objects is a weak equivalence in this model structure if and only if it is a pointwise weak equivalence in the sense of Definition 1.6.
(iii) More generally, for $X \in \mathfrak{SE}$, a map in $\mathfrak{SE} \nmid X$ is a weak equivalence exactly if and only if it is a pointwise weak equivalence in $\mathfrak{SE}$ in the sense of Definition 1.6.

*Proof.* First note that $\mathfrak{SE}$ has finite limits by lextensivity and the required colimits of a model structure by the same reasoning used for Proposition 9.6. We define the class of weak equivalences to be $\mathbf{W}$. It satisfies 2-out-of-3 by Corollary 9.4. It remains to show that a (co)fibration is trivial exactly if it is a weak equivalence.

Due to our definition of $\mathbf{W}$, we get for free that every trivial fibration is a weak equivalence, dually to the reasoning for trivial cofibrations in Proposition 9.6.

For the reverse direction, let $X \to Y$ be a fibration and weak equivalence. Let $\widehat{X} \to \widehat{Y}$ denote its canonical cofibrant replacement. This is the Reedy cofibrant replacement over the inverse category [1], hence again a fibration. Since $\widehat{X} \to \widehat{Y}$ is a fibration and weak equivalence in $\mathcal{E}_{\mathrm{cof}}$, it is a trivial fibration by Proposition 9.6. The composite $\widehat{X} \to Y$ is a trivial fibration by part (ii) of Lemma 1.5. By part (iii) of Lemma 1.5, we deduce that $X \to Y$ is a trivial fibration.

Let $A \to B$ be a trivial cofibration. Take a cofibrant replacement $\widehat{B} \to B$. Let $\widehat{A} \to A$ be its pullback along $A \to B$. Then $\widehat{A}$ is cofibrant by Lemma 5.7 since trivial cofibrations are monomorphisms by Proposition 5.2, $\widehat{A} \to A$ is a trivial fibration by part (ii) of Lemma 1.5, and $\widehat{A} \to \widehat{B}$ is a trivial cofibration by Proposition 7.6. In particular, $\widehat{A} \to \widehat{B}$ is a cofibrant replacement of $A \to B$. Since it is a trivial cofibration, it is a weak equivalence in $\mathcal{E}_{\mathrm{cof}}$ by Proposition 9.6. By Lemma 9.7, this makes $A \to B$ is a weak equivalence.

It remains to show that every cofibration that is a weak equivalence is a trivial cofibration. As in Proposition 9.6, this follows from what we have already established by the retract argument.

47