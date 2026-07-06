10

A Substitution Algorithm for Multimode Type Theory: Technical Report

\(\operatorname{embed}((\mu \mid A) \to B) = (\mu \mid \operatorname{embed}(A)) \to \operatorname{embed}(B)\)

\(\operatorname{embed}(\lambda^{\mu}(t)) = \lambda^{\mu}(\operatorname{embed}(t))\)

\(\operatorname{embed}(\operatorname{app}_{\mu}(f; t)) = \operatorname{app}_{\mu}(\operatorname{embed}(f); \operatorname{embed}(t))\)

\(\operatorname{embed}(\langle \mu \mid A \rangle) = \langle \mu \mid \operatorname{embed}(A) \rangle\)

\(\operatorname{embed}(\operatorname{mod}_{\mu}(t)) = \operatorname{mod}_{\mu}(\operatorname{embed}(t))\)

\(\operatorname{embed}(\operatorname{letmod}_{\nu, \mu}(A; B; t; s)) = \operatorname{letmod}_{\nu, \mu}(\operatorname{embed}(A); \operatorname{embed}(B); \operatorname{embed}(t); \operatorname{embed}(s))\)

Embedding SFMTT rensubs (atomic and regular) to WSMTT substitutions is defined as follows.

\(\begin{array}{ll}\operatorname{embed}(!) = ! & \operatorname{embed}\left(\mathbf{Q}_{\hat{\Gamma}}^{\alpha \in \Lambda \Rightarrow \Theta}\right) = \mathbf{Q}_{\hat{\Gamma}}^{\alpha \in \Lambda \Rightarrow \Theta}\\ \operatorname{embed}(\mathrm{id}^{\mathrm{a}}) = \mathrm{id} & \operatorname{embed}(\sigma .t) = \operatorname{embed}(\sigma). \operatorname{embed}(t)\\ \operatorname{embed}(\operatorname{weaken}(\sigma)) = \operatorname{embed}(\sigma)\circ \pi & \operatorname{embed}(\mathrm{id}) = \mathrm{id}\\ \operatorname{embed}(\sigma .\widehat{\mathbf{Q}}_{\mu}) = \operatorname{embed}(\sigma).\widehat{\mathbf{Q}}_{\mu} & \operatorname{embed}(\sigma \odot \tau) = \operatorname{embed}(\sigma)\circ \operatorname{embed}(\tau) \end{array}\)

## 4 Completeness

We want to prove the statement that our substitution algorithm is complete with respect to the notion of  \( \sigma \) -equivalence introduced in Figure 4. In other words, whenever two WSMTT expressions are  \( \sigma \) -equivalent our algorithm should produce the same result.

Theorem 1. If we can deduce \(\hat{\Gamma} \vdash_{\mathrm{ws}} t \equiv^{\sigma} s \exp @ m\), then we have that \([t] = [s]\).

Before we can prove this theorem, we need some technical machinery that will be developed in the next sections.

### 4.1 Observational Equivalence of SFMTT Substitutions

#### 4.1.1 Definition & Proof Technique (Part 1)

Recall that  \( \sigma \) -equivalence for WSMTT expressions is defined mutually recursively with  \( \sigma \) -equivalence for WSMTT substitutions (see Figure 4). Therefore, in order to prove Theorem 1, we need to first extend it so as to also make a claim about  \( \sigma \) -equivalent WSMTT substitutions. However, in SFMTT, syntactic equality of substitutions is not a good notion of equivalence. Instead, we will use the following:

▶ Definition 2 (Observational equivalence). We say that two SFMTT substitutions  \( \vdash_{sf} \sigma, \tau \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m \)  are observationally equivalent when  \( t [\sigma]_{sub} = t [\tau]_{sub} \)  for every expression  \( \hat{\Delta} \vdash_{sf} t \exp @ m \) . We will write this as  \( \sigma \approx^{obs} \tau \) .

Note that  \( \approx^{obs} \)  is clearly an equivalence relation. The requirement for two SFMTT substitutions to be observationally equivalent is quite strong. In order to prove this, we will make use of the technique outlined in Propositions 3 and 12. Both propositions refer to general scoping telescopes which may contain both variables and locks, see Figure 9 for their definition. We will refer to such scoping telescopes with the Greek letter  \( \Phi \) . They also act on SFMTT substitutions in the following way.

\(\sigma .\cdot = \sigma\)   
\(\sigma .(\Phi .\mu) = (\sigma .\Phi)^{+}\)   
\(\sigma .(\Phi .\widehat{\mathbf{Q}}_{\mu}) = (\sigma .\Phi).\widehat{\mathbf{Q}}_{\mu}\)