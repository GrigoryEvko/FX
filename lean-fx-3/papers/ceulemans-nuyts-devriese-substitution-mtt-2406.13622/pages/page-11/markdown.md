J. Ceulemans, A. Nuyts and D. Devriese

11

|  STELE-EMPTY | STELE-EXTEND | STELE-LOCK  |
| --- | --- | --- |
|  \( \cdot : \mathsf{sTele}(m \to m) \) | \( \Phi : \mathsf{sTele}(n \to m) \quad \mu : o \to m \) | \( \Phi : \mathsf{sTele}(n \to m) \quad \mu : o \to m \)  |
|  \( \hat{\Gamma} \cdot \cdot = \hat{\Gamma} \) | \( \Phi \cdot \mu : \mathsf{sTele}(n \to m) \) | \( \Phi \cdot \widehat{\mathbf{\Omega}}_{\mu} : \mathsf{sTele}(n \to o) \)  |
|   | \( \hat{\Gamma} \cdot (\Phi \cdot \mu) = (\hat{\Gamma} \cdot \Phi) \cdot \mu \) | \( \hat{\Gamma} \cdot (\Phi \cdot \widehat{\mathbf{\Omega}}_{\mu}) = (\hat{\Gamma} \cdot \Phi) \cdot \widehat{\mathbf{\Omega}}_{\mu} \)  |

Figure 9 Definition of scoping telescopes and how to append them to a scoping context (note that a scoping telescope \(\Phi : \mathsf{sTele}(n \to m)\) can be appended to a scoping context at mode \(n\) to obtain a scoping context at mode \(m\))

(Recall that the \(\widehat{\mathbf{\Omega}}_{\mu}\) and \(^+\) operations on SFMTT substitutions apply the corresponding operations to all atomic substitutions.) In other words, whenever \(\vdash_{\mathrm{sf}} \sigma \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m\) is an SFMTT substitution and \(\Phi : \mathsf{sTele}(m \to n)\) a scoping telescope, we get an SFMTT substitution \(\vdash_{\mathrm{sf}} \sigma \cdot \Phi \operatorname{sub}(\hat{\Gamma} \cdot \Phi \to \hat{\Delta} \cdot \Phi) @ n\).

▶ Proposition 3. Let  \( \vdash_{sf} \sigma, \tau \text{ sub}(\hat{\Gamma} \to \hat{\Delta}) @ m \)  be two SFMTT substitutions and suppose that  \( v [\sigma \cdot \Phi]_{\text{sub}} = v [\tau \cdot \Phi]_{\text{sub}} \)  for every scoping telescope  \( \Phi : sTele(m \to n) \)  and every variable  \( \hat{\Delta} \cdot \Phi \vdash_{sf} v \text{ var } @ n \) . Then  \( \sigma \approx^{obs} \tau \) .

Proof. We will prove that \( t[\sigma \cdot \Phi]_{\mathrm{sub}} = t[\tau \cdot \Phi]_{\mathrm{sub}} \) for all \( \Phi : \mathsf{sTele}(m \to n) \) and all expressions \( \hat{\Delta} \cdot \Phi \vdash_{\mathrm{sf}} t \exp @n \). The result then follows by taking \( \Phi \) to be the empty scoping telescope.

The proof proceeds by induction and case analysis on the expression \( t \). We will describe only a few cases since there is a lot of similarity.

CASE \(\hat{\Delta}.\Phi\vdash_{\mathrm{sf}}v\operatorname{expr}@n\) for some \(\hat{\Delta}.\Phi\vdash_{\mathrm{sf}}v\operatorname{var}@n\) (SF-EXPR-VAR)

In this case the assumptions of the proposition we are proving tell us exactly that \( v[\sigma, \Phi]_{\mathrm{sub}} = v[\tau, \Phi]_{\mathrm{sub}} \).

CASE \(\hat{\Delta}.\Phi\vdash_{\mathrm{sf}}\lambda^{\mu}(t)\) expr @ \(n\) for some \(\hat{\Delta}.\Phi.\mu\vdash_{\mathrm{sf}}t\) expr @ \(n\) (SF-EXPR-LAM)

Recall that an SFMTT substitution is just a sequence of atomic SFMTT substitutions which are applied sequentially to an expression. Following Equation (9) each of these atomic substitutions will be pushed through the  \( \lambda^{\mu} \)  constructor, applying a lifting  \( (^{+}) \)  to that atomic substitution. Since the lifting of regular SFMTT substitutions applies the lifting to all its constituent atomic substitutions, we have that

\[
\left(\lambda^ {\mu} (t)\right) [ \sigma . \Phi ] _ {\mathrm{sub}} = \lambda^ {\mu} \left(t [ (\sigma . \Phi) ^ {+} ] _ {\mathrm{sub}}\right) = \lambda^ {\mu} \left(t [ \sigma . (\Phi . \mu) ] _ {\mathrm{sub}}\right),
\]

and similar for \(\tau\). We can now apply the induction hypothesis for the structurally smaller term \(t\) to obtain that \(t[\sigma, (\Phi, \mu)]_{\mathrm{sub}} = t[\tau, (\Phi, \mu)]_{\mathrm{sub}}\).

CASE \(\hat{\Delta}.\Phi\vdash_{\mathrm{sf}}\mathrm{mod}_{\mu}(t)\) expr @ \(n\) for some \(\hat{\Delta}.\Phi.\widehat{\mathbf{\Omega}}_{\mu}\vdash_{\mathrm{sf}}t\) expr @ \(o\) (SF-EXPR-MOD-TM)

We can follow a similar style of reasoning as in the previous case, taking into account that applying a lock to a regular SFMTT substitution applies that lock to all constituent atomic substitutions. Using Equation (12) for every atomic substitution, we then get that

\[
\left(\operatorname{mod} _ {\mu} (t)\right) [ \sigma . \Phi ] _ {\text {sub}} = \operatorname{mod} _ {\mu} \left(t [ (\sigma . \Phi). \widehat {\mathbf {\Omega}} _ {\mu} ] _ {\text {sub}}\right) = \operatorname{mod} _ {\mu} \left(t [ \sigma . (\Phi . \widehat {\mathbf {\Omega}} _ {\mu}) ] _ {\text {sub}}\right),
\]

and similar for \(\tau\). The induction hypothesis for \(t\) gives us that \(t[\sigma, (\Phi, \widehat{\mathbf{\Omega}}_{\mu})]_{\mathrm{sub}} = t[\tau, (\Phi, \widehat{\mathbf{\Omega}}_{\mu})]_{\mathrm{sub}}\).

#### 4.1.2 Mixed Sequences of Atomic Rensubs

Using Proposition 3 to prove observational equivalence is still far from trivial. Therefore, Proposition 12 will relax the requirement so that we only have to check the equality of