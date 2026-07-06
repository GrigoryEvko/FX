28

A Substitution Algorithm for Multimode Type Theory: Technical Report

## 5 Soundness

We want to prove the soundness of our substitution algorithm with respect to the notion of  \( \sigma \) -equivalence introduced in Figure 4. In other words, whenever we compute all substitutions away in a WSMTT expression t, the result should be  \( \sigma \) -equivalent to the expression t we started from.

Theorem 25. Let \(\hat{\Gamma} \vdash_{\mathrm{ws}} t \exp @ m\) be a WSMTT expression. Then we have that \(\hat{\Gamma} \vdash_{\mathrm{ws}} \operatorname{embed}([t]) \equiv^{\sigma} t \exp @ m\).

The proof of this theorem appears at the end of this section.

### 5.1 Embedding of SFMTT into WSMTT

Note that in Section 3.3 we first defined an embedding of SFMTT expressions to WSMTT and then an embedding for atomic and regular rensubs. This is unlike the translation function from WSMTT to SFMTT, which is defined mutually recursively for expressions and substitutions. The reason for this is that SFMTT substitutions do not occur in the syntax of SFMTT expressions. However, the proof of Theorem 25 is easier to formulate if we do have an embedding of rensubs at our disposal. In particular, the core result for proving soundness will be Proposition 34.

In this section on the soundness proof, we will extensively use the fact that composition of WSMTT substitutions is associative and that id is its unit, all up to  \( \sigma \) -equivalence. Moreover, congruence rules with respect to WSMTT  \( \sigma \) -equivalence will also regularly be used. We will not explicitly mention the use of any of these rules from Figure 4.

▶ Example 26 (Embedding does not preserve observational equivalence). Given that we have introduced the notion of observational equivalence for SFMTT substitutions in Section 4.1, it is natural to ask whether  \( \sigma \approx^{obs} \tau \)  implies  \( \text{embed}(\sigma) \equiv^{\sigma} \text{embed}(\tau) \) . The answer is no, and we can give a counterexample similar to Example 13. Again, let the mode theory be the walking arrow. Let  \( \hat{\Gamma} = (\cdot \widehat{\mathbf{B}}_{\mu}) \)  and  \( \hat{\Delta} = (\cdot \mathbb{1} \widehat{\mathbf{B}}_{\mu}) \) . As argued in Example 13, all substitutions to  \( \hat{\Delta} \)  are observationally equivalent. However, the embeddings of  \( \vdash_{sf} (!true \widehat{\mathbf{B}}_{\mu}), (!false \widehat{\mathbf{B}}_{\mu}) \)  asub( \( \hat{\Gamma} \to \hat{\Delta} \) ) @ m are not  \( \sigma \) -equivalent.

▶ Lemma 27. For an SFMTT renaming or substitution  \( \vdash_{sf} \sigma \operatorname{ren}/\operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m \)  we have that  \( \vdash_{ws} \operatorname{embed}(\sigma^{+}) \equiv^{\sigma} \operatorname{embed}(\sigma)^{+} \operatorname{sub}(\hat{\Gamma}. \mu \to \hat{\Delta}. \mu) @ m \) .

Proof. Since  \( id^{+} \equiv^{\sigma} id \)  and  \( (\sigma \circ \tau)^{+} \equiv^{\sigma} \sigma^{+} \circ \tau^{+} \)  (which can be proved using WSMTT-EQ-SUB-EXTEND-WEAKEN, WSMTT-EQ-SUB-EXTEND-ETA and WSMTT-EQ-EXPR-EXTEND-VAR), it suffices to prove this for an atomic rensub  \( \sigma \) . Then we have that

\(\begin{array}{ll}\mathsf{embed}(\sigma^{+})\\ = \mathsf{embed}\Big(\mathsf{weaken}(\sigma).\mathbf{v}_{0}^{1_{\mu}}\Big) & (\text{SFMTT definition of }^{+},(3))\\ = (\mathsf{embed}(\sigma)\circ \pi).\Big(\mathbf{v}_{0}\left[\mathbf{a}_{\hat{\Gamma},\mu}^{1_{\mu}\in \hat{\mathbf{B}}_{\mu}\Rightarrow \hat{\mathbf{B}}_{\mu}}\right]_{\mathrm{ws}}\Big) & (\text{Definition of embed} (\_))\\ \equiv^{\sigma}(\mathsf{embed}(\sigma)\circ \pi).\mathbf{v}_{0} & (\text{WSMTT-EQ-SUB-KEY-UNIT})\\ = \mathsf{embed}(\sigma)^{+}. & (\text{WSMTT definition of }^{+},(1)) \end{array}\)