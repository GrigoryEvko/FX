J. Ceulemans, A. Nuyts and D. Devriese

3

context $\hat{\Gamma}, \mathbf{\Theta}_{\mu}$ (WSMTT-EXPR-APP). Furthermore, there are the WSMTT versions of the formation (WSMTT-EXPR-MOD-TY) and introduction (WSMTT-EXPR-MOD-TM) for modal types rules from MTT. The modal eliminator (WSMTT-EXPR-MOD-ELIM) corresponds to the MTT expression constructor let, $\text{mod}_{\mu}(x) = t$ in $s$, which allows us to view a term $t$ of type $\langle \mu \mid A \rangle$ as if it were of the form $\text{mod}_{\mu}(x)$ when type checking the term $s$. We refer to [2] for more details on this modal eliminator, as its behaviour with respect to substitution is not special and it does otherwise not play an important role in this report.

We emphasize again that all expression and substitution constructors in WSMTT can be obtained by removing the typing information from the corresponding constructors in MTT.

## 2.2 $\sigma$-equivalence

To recall the notation, we make use of a judgement $\hat{\Gamma} \vdash_{\text{ws}} t \equiv^{\sigma} s \text{ expr } @m$ for $\sigma$-equivalence of WSMTT expressions and $\vdash_{\text{ws}} \sigma \equiv^{\sigma} \tau \text{ sub}(\hat{\Gamma} \to \hat{\Delta}) @m$ for $\sigma$-equivalence of WSMTT substitutions. Figure 6 in the paper only provides some of the rules for $\sigma$-equivalence. In this section we spell out the full definition, or at least give a description of what the full definition should look like. Most of the rules for $\sigma$-equivalence can be found in Figure 4. All rules fall into different classes and for each class we describe the rules that have been omitted:

- There are rules expressing that $\sigma$-equivalence of expressions and substitutions are equivalence relations (reflexivity, symmetry, transitivity). We show just the rule for reflexivity in Figure 4 (WSMTT-EQ-EXPR-REFL).

- Given a mode $m$, we have a category $\text{SCtx}_m$ of scoping contexts at $m$. Its objects are given by scoping contexts and morphisms by substitutions. In order to have a category, we add rules that establish the associativity of composition and the fact that id is a unit of $\circ$. We show just 1 rule in Figure 4, namely WSMTT-EQ-SUB-ID-RIGHT.

- There are rules that express the functoriality of explicit substitution in expressions, i.e. expressions involving the identity (WSMTT-EQ-EXPR-SUB-ID) and composite substitutions (WSMTT-EQ-EXPR-SUB-COMPOSE).

- For every expression and substitution constructor that takes some arguments, there are rules expressing that it preserves $\sigma$-equivalence. We show the rules for $\_ [\_]_{\text{ws}}$ (WSMTT-EQ-EXPR-CONG-SUB), $\lambda^{\mu} (\_)$ (WSMTT-EQ-EXPR-CONG-LAM), $\text{app}_{\mu} (\_; \_)$ (WSMTT-EQ-EXPR-CONG-APP), $\_ \circ \_$ (WSMTT-EQ-SUB-CONG-COMPOSE), $\_.\_$ (WSMTT-EQ-SUB-CONG-EXTEND) and $\_,\mathbf{\Theta}_{\mu}$ (WSMTT-EQ-SUB-CONG-LOCK).

- Furthermore, we have for every expression constructor a rule expressing how substitutions can be pushed through them. We explicitly show the rules for $\lambda^{\mu} (\_)$ (WSMTT-EQ-EXPR-LAM-SUB) and $\text{app}_{\mu} (\_; \_)$ (WSMTT-EQ-EXPR-APP-SUB). Note that we make use of a lifting operation on WSMTT substitutions which is defined as follows.

$$\sigma^{+} := (\sigma \circ \pi).\mathbf{v}_{0} \tag{1}$$

- The CwF rules governing the empty context (WSMTT-EQ-SUB-EMPTY-UNIQUE) and context extension (WSMTT-EQ-EXPR-EXTEND-VAR, WSMTT-EQ-SUB-EXTEND-WEAKEN and WSMTT-EQ-SUB-EXTEND-ETA) are also present, but the ones for context extension are adapted to our modal situation, taking into account that variables are annotated with a modality in the context and that the extension constructor for substitutions takes a term that lives in a locked context.

- We have two strict 2-categories in play: the mode theory $\mathcal{M}$ and Cat, the 2-category of categories. We add rules to ensure that the intrinsically scoped WSMTT syntax