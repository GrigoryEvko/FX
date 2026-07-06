Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:45

is not until we introduce rules for extent and Gel that the structural interval ceases to model the theory.

On the cubical side, we can treat path interval variables in the same way as term variables. However, we also need the principle that bridge and path variables can be exchanged.

$$\begin{array}{c c c} \text {SUBST-}\mathbb {I} & & \text {SUBST-\text {II}} \\ \Gamma \vdash \delta : \Delta & \Delta \vdash r: \mathbb {I} & \text {SUBST-PROJ-}\mathbb {I} \\ \hline \Gamma \vdash \delta . r: \Delta . \mathbb {I} & & \overline {{\Gamma . \mathbb {I} \vdash p _ {\mathbb {I}} : \Gamma}} \\ & & \overline {{\Gamma . \mathbf {I} . \mathbb {I} \vdash \mathrm {ex} _ {\mathbb {I} \mathbf {I}} : \Gamma . \mathbb {I} . \mathbf {I}}} \end{array}$$

The substitution $\mathrm{ex}_{\mathbb{I}}$ serves to invert the substitution $\Gamma.\mathbb{I}.\mathbf{I} \vdash \mathsf{p}_{\mathbb{I}}^{\mathbf{I}}.\mathsf{q}_{\mathbb{I}}[\mathsf{p}_{\mathbb{I}}] : \Gamma.\mathbf{I}.\mathbb{I}$, and expresses that path terms are always apart from bridge terms. Besides this principle, the cubical and parametric sides of the theory only interact via the allowance for bridge constraints in hcom terms and the inclusion of rules for computing Kan operations in Bridge- and Gel-types, which we may formulate following the operational semantics shown in Figure 2.

5.2. Type and term formers. With the judgmental infrastructure in place, it is fairly straightforward to translate the computational type formers introduced in Section 2 to the formal setting. We describe the rules for Bridge-types here; rules for Gel-types and extent may be found in Appendix A. The formation, introduction, and elimination rules for Bridge-types follow exactly the pattern of Figure 4.

$$\frac {\Gamma . \mathbf {I} \vdash A \text {type} \quad \Gamma \vdash M _ {0} : A [ \mathbf {0} _ {\mathbf {I}} ] \quad \Gamma \vdash M _ {1} : A [ \mathbf {1} _ {\mathbf {I}} ]}{\Gamma \vdash \operatorname{Bridge} _ {A} (M _ {0} , M _ {1}) \text {type}} \quad \frac {\Gamma . \mathbf {I} \vdash A \text {type} \quad \Gamma . \mathbf {I} \vdash M : A}{\Gamma \vdash \lambda^ {\mathbf {I}} . M : \operatorname{Bridge} _ {A} (M [ \mathbf {0} _ {\mathbf {I}} ] , M [ \mathbf {1} _ {\mathbf {I}} ])}$$

$$\frac {\Gamma . \backslash \boldsymbol {r} \vdash M _ {0} : A [ \mathbf {0} _ {\mathbf {I}} ] \qquad \begin{array}{c} \Gamma \vdash \boldsymbol {r} : \mathbf {I} \qquad \Gamma . \backslash \boldsymbol {r} . \mathbf {I} \vdash A \text {type} \\ \Gamma . \backslash \boldsymbol {r} \vdash M _ {1} : A [ \mathbf {1} _ {\mathbf {I}} ] \qquad \Gamma . \backslash \boldsymbol {r} \vdash P : \operatorname{Bridge} _ {A} (M _ {0} , M _ {1}) \end{array}}{\Gamma \vdash P @ \boldsymbol {r} : A [ \mathrm{id} . \boldsymbol {r} ]}$$

It is the elimination rule—along with the rules for extent and Gel-types—that necessitates the introduction of the interval restriction operator. In [BCM15], bridge elimination is instead described by a rule of the following kind.

$$\frac {\Gamma . \mathbf {I} \vdash A \text {type} \qquad \Gamma \vdash M _ {0} : A [ \mathbf {0} _ {\mathbf {I}} ] \qquad \Gamma \vdash M _ {1} : A [ \mathbf {1} _ {\mathbf {I}} ] \qquad \Gamma \vdash P : \operatorname{Bridge} _ {A} (M _ {0} , M _ {1})}{\Gamma . \mathbf {I} \vdash \operatorname{app} (P) : A}$$

This form of elimination is inter-derivable with our own: one may set $P@\boldsymbol{r} := \mathsf{app}(P)[\mathsf{id}.\boldsymbol{r}]$ or conversely $\mathsf{app}(P) := P[\mathsf{id}^{\dagger}]@\mathsf{q}_{\mathbf{I}}$. However, the [BCM15] rule produces a formalism in which substitution is not admissible, that is, a theory in which not every term is equal to one containing no use of the $-[-]$ operator. Given $P$ as in the rule and a substitution $\Delta \vdash \gamma : \Gamma.\mathbf{I}$, there is no way to reduce the term $\mathsf{app}(P)[\gamma]$ unless it happens that $\Delta = \Delta'.\mathbf{I}$ and $\gamma = \gamma'^{\mathbf{I}}$ for some $\Delta' \vdash \gamma' : \Gamma$, in which case $\mathsf{app}(P)[\gamma] = \mathsf{app}(P[\gamma'])$. By contrast, we may reduce a term $(P@\boldsymbol{r})[\gamma]$ using the functorial action of restriction, as prescribed by the rule below.