Cubical set model 285

counit substitutions. We note again the similarity between these rules and the rules for the bridge type, with dsc playing the rule of $-\cdot\mathbf{I}$ and cc the role of $-\cdot\mathbf{r}$.

$$\frac{\Gamma.\text{dsc} \vdash A \text{ type @ par}}{\Gamma \vdash \text{Glo}(A) \text{ type @ pt}} \qquad \frac{\Gamma.\text{dsc} \vdash M : A \text{ @ par}}{\Gamma \vdash \text{mod}(M) : \text{Glo}(A) \text{ @ pt}}$$

$$\frac{\Gamma.\text{cc.dsc} \vdash A \text{ type @ m}}{\Gamma \vdash \text{unmod}(M) : A[\{\text{unit}\}] \text{ @ m}} \qquad \frac{\Gamma.\text{cc} \vdash M : \text{Glo}(A) \text{ @ n}}{}$$

$$\frac{\Gamma.\text{cc.dsc} \vdash A \text{ type @ m}}{\Gamma \vdash \text{unmod}(\text{mod}(M)) = M[\{\text{unit}\}] : A[\{\text{unit}\}] \text{ @ m}} \qquad \frac{\Gamma.\text{cc.dsc} \vdash M : A \text{ @ m}}{}$$

$$\frac{\Gamma.\text{dsc} \vdash A \text{ type @ m}}{\Gamma \vdash M = \text{mod}(\text{unmod}(M[\{\text{cou}\}])) : \text{Glo}(A) \text{ @ n}} \qquad \frac{\Gamma \vdash M : \text{Glo}(A) \text{ @ n}}{}$$

**Discrete type** Finally, our formal rules for the discrete type likewise mimic the suite of rules proven in Section 14.4.2.

$$\frac{\Gamma.\text{cc} \vdash A \text{ type @ par}}{\Gamma \vdash \text{Disc}(A) \text{ type @ pt}} \qquad \frac{\Gamma.\text{cc} \vdash M : A \text{ @ par}}{\Gamma \vdash \text{mod}(M) : \text{Disc}(A) \text{ @ pt}}$$

$$\frac{\Gamma.\text{cc} \vdash A \text{ type @ pt}}{\Gamma \vdash P : \text{Disc}(A) \text{ @ par}} \qquad \frac{\Gamma.\text{Disc}(A) \vdash B \text{ type @ par}}{\Gamma.(\text{cc} \mid A) \vdash N : B[\text{p.mod}(v)] \text{ @ par}}{\Gamma \vdash \text{letdisc}(B, P, N) : B[\text{id.P}] \text{ @ par}}$$

$$\frac{\Gamma.\text{cc} \vdash A \text{ type @ pt}}{\Gamma.\text{cc} \vdash M : A \text{ @ par}} \qquad \frac{\Gamma.\text{Disc}(A) \vdash B \text{ type @ par}}{\Gamma.(\text{cc} \mid A) \vdash N : B[\text{p.mod}(v)] \text{ @ par}}{\Gamma \vdash \text{letdisc}(B, \text{mod}(M), N) = N[\text{id.M}] : B[\text{id.mod}(M)] \text{ @ par}}$$

## 16.1 Cubical set model

To construct a model in cubical sets, we combine the pointwise and parametric models described in Sections 3.3.1 and 11.1 respectively. We interpret judgments in the pointwise mode as statements about the category $PSh(\widehat{\mathbb{D}}_c)$ of cartesian cubical sets and judgments in the parametric mode as statements about the category $PSh(\widehat{\mathbb{D}}_{c \times a})$ of cartesian-affine bicubical sets. Henceforth we rename $\widehat{\mathbb{D}}_c$ and $\widehat{\mathbb{D}}_{c \times a}$ to $\widehat{\mathbb{D}}_{\text{pt}}$ and $\widehat{\mathbb{D}}_{\text{par}}$ respectively to reflect their roles.