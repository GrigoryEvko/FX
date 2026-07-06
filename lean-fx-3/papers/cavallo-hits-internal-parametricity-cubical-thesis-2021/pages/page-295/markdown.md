283

These are required to satisfy various equations we will not list explicitly: triangle equalities relating the unit and counit of each adjunction, the fact that $\text{cou}^{-1}$ and $\text{unit}^{-1}$ provide the inverses suggested by the notation, and the laws of a strict 2-category [JY20, Proposition 2.3.4].

**Contexts** The collection of context formers is now extended with the application of modalities, modal hypotheses, and endpoint hypotheses. Like other operations defined by recursion in the computational framework—substitution, interval restriction—the application of a modality here becomes a primitive context former.

$$\frac{\Gamma \operatorname{ctx} @ n \quad \mu : m \to n}{\Gamma . \mu \operatorname{ctx} @ m} \quad \frac{\mu : m \to n \quad \Gamma . \mu \vdash A \operatorname{type} @ m}{\Gamma . (\mu \mid A) \operatorname{ctx} @ n} \quad \frac{\Gamma \operatorname{ctx} @ m}{\Gamma . 2 \operatorname{ctx} @ m}$$
$$\frac{\Gamma . \operatorname{id} = \Gamma \operatorname{ctx} @ m}{\Gamma . \operatorname{id} = \Gamma \operatorname{ctx} @ m} \quad \frac{\nu : n \to p \quad \mu : m \to n}{\Gamma . (\nu \otimes \mu) = \Gamma . \nu . \mu \operatorname{ctx} @ m}$$

**Modalities in substitutions** Each modality has a functorial action on substitutions, and each 2-cell moreover induces a substitution between modal contexts. These are required to preserve the 2-categorical structure—for example, we require $\Gamma' \vdash \gamma \otimes \operatorname{id} = \gamma : \Gamma @ m$—and we ask that each substitution $\{\alpha\}$ satisfies a naturality condition as shown below.

$$\frac{\mu : m \to n \quad \Gamma' \vdash \gamma : \Gamma @ n}{\Gamma' . \mu \vdash \gamma \otimes \mu : \Gamma . \mu @ m} \quad \frac{\alpha :: \mu \Rightarrow \nu : m \to n}{\Gamma . \nu \vdash \{\alpha\} : \Gamma . \mu @ m}$$

$$\frac{\alpha :: \mu \Rightarrow \nu : m \to n \quad \Gamma' \vdash \gamma : \Gamma}{\Gamma' . \nu \vdash \{\alpha\} \circ (\gamma \otimes \nu) = (\gamma \otimes \mu) \circ \{\alpha\} : \Gamma . \mu @ m}$$

The rule for forming substitutions into a modal hypothesis matches the computational definition, and the variable rule is as in Theorem 14.3.15.

$$\frac{\mu : m \to n \quad \Gamma' \vdash \gamma : \Gamma @ n \quad \Gamma . \mu \vdash A \operatorname{type} @ m \quad \Gamma' . \mu \vdash M : A[\gamma \otimes \mu] @ m}{\Gamma' \vdash \gamma . M : \Gamma . (\mu \mid A) @ n}$$

$$\frac{\mu : m \to n \quad \Gamma . \mu \vdash A \operatorname{type} @ m}{\Gamma . (\mu \mid A) . \mu \vdash \nu : A[\mathrm{p} \otimes \mu] @ m}$$