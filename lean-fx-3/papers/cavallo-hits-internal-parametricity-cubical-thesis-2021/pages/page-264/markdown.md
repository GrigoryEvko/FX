252

Cohesive parametric type theory

### 14.3.2 Contexts and substitutions

Finally, we use the properties of the extended closing substitutions to bootstrap our way to the open judgments and then general substitutions. The first main result is that \(-.\mu\) preserves well-formed contexts, which follows from the division lemma foreshadowed in the previous section.

Lemma 14.3.12 (Division of open judgments). Let \(\mu : m \to n\) and \(\nu : p \to m\) be given and assume \(\mu \div \nu\) is defined.

- Given \(\Gamma.\mu \gg A = A'\) pretype @ \(m\), we have \(\Gamma.\nu.(\mu \div \nu) \gg A = A'\) pretype @ \(m\).
- Given \(\Gamma.\mu \gg M = M' \in A @ m\), we have \(\Gamma.\nu.(\mu \div \nu) \gg M = M' \in A @ m\).

Proof. Without loss of generality we focus on the first property; we go by definition of the open pretype judgment. Let closing substitutions \(\Psi \Vdash \gamma = \gamma' \in \Gamma.\nu.(\mu \div \nu) @ m\) be given. By Lemma 14.3.11, we derive substitutions \(\Psi \Vdash \gamma_{+} = \gamma_{+}' \in \Gamma.\mu @ m\). Then by definition of \(\Gamma.\mu \gg A = A'\) pretype @ \(m\), we have \(\Psi \Vdash A\gamma_{+} = A'\gamma_{+}'\) pretype @ \(m\), which is to say \(\Psi \Vdash A\gamma = A'\gamma'\) pretype @ \(m\).

Theorem 14.3.13 (Modal context operators).

$$\frac{\Gamma = \Gamma' \operatorname{ctx} @ n \quad \mu : m \to n}{\Gamma.\mu = \Gamma'.\mu \operatorname{ctx} @ m}$$

Proof. By induction on \(\Gamma = \Gamma' \operatorname{ctx} @ n\), using Lemma 14.3.12 in the modal hypothesis case.

The second essential result is the variable rule for modal hypotheses.

Lemma 14.3.14. For any \(\mu : m \to n\), \((\mu \div \mu)\) is defined and does not contain glo.

Proof. After generalizing to the claim that \((\nu, \mu) \div \mu\) is defined and does not contain glo for any \(\nu : n \to n\) not containing glo, this follows straightforwardly by induction on \(\mu\).

Theorem 14.3.15 (Variable).

$$\frac{\mu : m \to n \quad \Gamma.\mu \gg A \text{ pretype } @ m}{\Gamma, (\mu \mid a : A).\mu \gg a \in A @ m}$$