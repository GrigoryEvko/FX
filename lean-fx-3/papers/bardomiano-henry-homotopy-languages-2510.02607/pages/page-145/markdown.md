Where $A$ and $B$ are cofibrant, $i$ is a cofibration, $X$ and $Y$ are fibrant, $p$ is a fibration and either $p$ or $i$ is a weak equivalence, then there exists a dotted map that makes the diagram to commute.

*Remark C.2.* In theorem C.1 we use the usual conventions: a *cofibrant object* is an object such that the unique map $0 \rightarrow X$ is a cofibration, and a *fibrant object* is an object such that the unique map $X \rightarrow 1$ is a fibration. A trivial (co)fibration is a map which is both an equivalence and a (co)fibration. We will also use the term *core cofibrations* to mean “cofibration between cofibrant objects” and *core fibrations* to mean “fibration between fibrant objects”.

*Remark C.3.* It is crucial to observe that theorem C.1 only involve the core cofibrations, core fibrations and weak equivalences between objects that are either fibrant or cofibrant. By that we mean that if given $\mathcal{M}$ a category with these three classes of maps, then ($\mathcal{M}$, cofibrations, fibrations, weak equivalences) is a weak model structure if and only if ($\mathcal{M}$, core cofibrations, core fibrations, weak equivalences between objects that are either fibrant or cofibrant) is a model structure.

For this reason, we generally consider that only core cofibrations, core fibrations and weak equivalence between objects that are either fibrant or cofibrant are to be treated as relevant notions. Nothing we will do here depends on the three class of maps outside these restrictions. In [Hen20] it was even considered that the words cofibrations, fibrations and weak equivalences to mean “core cofibrations”, “core fibrations” and “weak equivalences between fibrant or cofibrant objects”.

*Remark C.4.* The definition of weak model structure in [Hen20] is different from theorem C.1, but it is equivalent. It is stated without reference to the class of weak equivalence, and using the notion of (weak relative) path object and cylinder object. It is easy to show that a weak model structure in the sense of theorem C.1 is a weak model structure in the sense of [Hen20] by constructing the cylinder and path objects as factorization of the codiagonal and diagonal maps (see C.5 below). Conversely, it is shown in [Hen20] that given a weak model structure, it admits a (unique$^6$) class of weak equivalences such that all conditions of theorem C.1 are satisfied.

It is shown in [Hen20] that most of the basic theory of Quillen model categories carries over to weak model categories, with only some additional

$^6$Keeping in mind theorem C.3. Only the class of weak equivalence between fibrant or cofibrant objects is uniquely defined, outside of this, there are no restriction whatsoever on weak equivalence from theorem C.1.

145