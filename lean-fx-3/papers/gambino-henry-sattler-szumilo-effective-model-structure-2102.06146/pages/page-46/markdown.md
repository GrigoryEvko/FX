In the following, we fix the following terminology regarding the weak factorisation systems of Theorem 4.2. A *fibrant replacement* of $X \in \mathfrak{s}\mathcal{E}$ is a trivial cofibration $X \rightarrow X'$ with $X'$ fibrant. By a fibrant replacement of a diagram, we mean a levelwise fibrant replacement: given a diagram $X: \mathcal{S} \rightarrow \mathfrak{s}\mathcal{E}$, this is a diagram $X': \mathcal{S} \rightarrow \mathfrak{s}\mathcal{E}_{\text{fib}}$ with a natural transformation $X \rightarrow X'$ that is levelwise a trivial cofibration. If $\mathcal{S}$ is a finite Reedy category, we can always construct such a replacement using Theorem 3.14 and the Reedy process. In particular, for [1] seen as a direct category, we obtain a fibrant replacement of any arrow that we call *canonical*. Note that the canonical fibrant replacement preserves trivial cofibrations. We use dual terminology for *cofibrant replacement*.

Let us write $\mathbf{W}_{\text{cof}}$ for the class of maps in $\mathfrak{s}\mathcal{E}_{\text{cof}}$ whose canonical fibrant replacement is a weak equivalence in $\mathfrak{s}\mathcal{E}_{\text{cof, fib}}$. This will be the class of weak equivalences in the model structure on $\mathfrak{s}\mathcal{E}_{\text{cof}}$ to be established in Proposition 9.6.

**Lemma 9.3.** *Let $A \rightarrow B$ in $\mathfrak{s}\mathcal{E}_{\text{cof}}$. Then, the the following are equivalent:*

- (i) *the map $A \rightarrow B$ is in $\mathbf{W}_{\text{cof}}$*,
- (ii) *the map $A \rightarrow B$ has a fibrant replacement that is a weak equivalence in $\mathfrak{s}\mathcal{E}_{\text{cof, fib}}$*,
- (iii) *all fibrant replacements of the map $A \rightarrow B$ are weak equivalences in $\mathfrak{s}\mathcal{E}_{\text{cof, fib}}$*.

*Proof.* This is a standard argument and goes exactly as in [GSS19, Lemma 3.3.1]. What is used is part (i) of Corollary 2.12 with the fact that trivial cofibrations are levelwise complemented inclusions (Proposition 3.17), and closure properties of trivial cofibrations (Lemma 3.9), the forward direction of part (i) of Lemma 9.2, and 2-out-of-3 for weak equivalences in $\mathfrak{s}\mathcal{E}_{\text{cof, fib}}$. $\square$

**Corollary 9.4.** *The class $\mathbf{W}_{\text{cof}}$ satisfies the 2-out-of-3 property.*

*Proof.* Using Lemma 9.3 with levelwise fibrant replacement of the given 2-out-of-3 diagram, this reduces to closure of weak equivalences in $\mathfrak{s}\mathcal{E}_{\text{cof, fib}}$ under 2-out-of-3. This is part of Theorem 1.7. $\square$

**Lemma 9.5.** *In $\mathfrak{s}\mathcal{E}_{\text{cof}}$, a fibration is a trivial fibration if and only if it is in $\mathbf{W}_{\text{cof}}$.*

*Proof.* Let $X \rightarrow Y$ be a fibration in $\mathfrak{s}\mathcal{E}_{\text{cof}}$. Take a fibrant replacement $Y \rightarrow \overline{Y}$.

If $X \rightarrow Y$ is a trivial fibration, we extend it to a trivial fibration $\overline{X} \rightarrow \overline{Y}$ using part (iii) of Lemma 9.1. Then $\overline{X} \rightarrow \overline{Y}$ is a weak equivalence by part (ii) of Lemma 9.2, hence $X \rightarrow Y$ is in $\mathbf{W}_{\text{cof}}$ by Lemma 9.3.

In the reverse direction, we extend $X \rightarrow Y$ to a fibration $\overline{X} \rightarrow \overline{Y}$ using part (ii) of Lemma 9.1. If $X \rightarrow Y$ is in $\mathbf{W}_{\text{cof}}$, then $\overline{X} \rightarrow \overline{Y}$ is a weak equivalence by Lemma 9.3, hence a trivial fibration by part (ii) of Lemma 9.2. Then its pullback $X \rightarrow Y$ is a trivial fibration by part (ii) of Lemma 1.5. $\square$

**Proposition 9.6.** *The category $\mathfrak{s}\mathcal{E}_{\text{cof}}$ admits a model structure with weak equivalences $\mathbf{W}_{\text{cof}}$ and the two weak factorisation systems of Theorem 4.2.*

*Proof.* First note that $\mathfrak{s}\mathcal{E}_{\text{cof}}$ has finite limits by part (iii) of Proposition 5.9, an initial object by lextensivity, and pushouts of cofibrations by part (i) of Corollary 2.12 (since cofibrations are levelwise complemented inclusions by Proposition 3.17). The class $\mathbf{W}_{\text{cof}}$ satisfies 2-out-of-3 by Corollary 9.4.

It remains to show that a (co)fibration is trivial exactly if it is a weak equivalence. For fibrations, this is Lemma 9.5. For cofibrations, the forward direction is immediate using Lemma 9.3: a given trivial cofibration has as fibrant replacement the identity on a fibrant replacement of its codomain; but identities are weak equivalences in $\mathfrak{s}\mathcal{E}_{\text{cof, fib}}$ by Theorem 1.7. The backward direction follows from this by the retract argument. $\square$

46