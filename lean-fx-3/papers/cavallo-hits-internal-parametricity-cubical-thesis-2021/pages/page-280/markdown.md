268 Programming in cohesive parametric type theory

coincidence that we have used the same syntax for the parametric and pointwise type formers.) As such, we cannot expect to show that any element of the pointwise $\mathbb{B}$ is path-equal to a $\mathfrak{t}$ or $\mathfrak{f}$. However, we *can* expect that any pointwise Church boolean that arises from a parametric Church boolean can be so characterized.

Within the pointwise mode, we have access to the type of parametric Church booleans via the global type $\mathrm{Glo}(\mathbb{B})$. Such a term is a polymorphic function defined for all elements of the parametric universe; by restricting it to discrete types, we can access its “underlying” pointwise function.

**Lemma 15.2.1.** We have a function $\mathrm{shadow} \in \mathrm{Glo}(\mathbb{B}) \to \mathbb{B} \text{ @ pt}$ defined as follows.

$$\mathrm{shadow}\,c := \lambda A.\,\lambda t.\,\lambda f.\,\mathrm{undisc}(\mathrm{unmod}(c)\,(\mathrm{Disc}(A))\,(\mathrm{mod}(t))\,(\mathrm{mod}(f)))$$

*Proof.* It is instructive to go through a typing derivation for the above term, working our way inward from the outside. By the introduction rule for functions, we must type the inner term in the context $\Gamma := (c : \mathrm{Glo}(\mathbb{B}), A : \mathrm{U}, t : A, f : A)$. Next we come to undisc. To apply **Lemma 15.1.2**, we must show the following.

$$\Gamma.\mathrm{dsc} \gg \mathrm{unmod}(c)\,(\mathrm{Disc}(A))\,(\mathrm{mod}(t))\,(\mathrm{mod}(f)) \in \mathrm{Disc}(A) \text{ @ par}$$

First, we have $\Gamma \gg c \in \mathrm{Glo}(\mathbb{B}) \text{ @ pt}$. As $\Gamma = \Gamma.\mathrm{dsc.cc}$, we can apply the projection for the global type to see that $\Gamma.\mathrm{dsc} \gg \mathrm{unmod}(c) \in \mathbb{B} \text{ @ par}$. Next, we have $\Gamma \gg A \text{ type @ pt}$; again using $\Gamma = \Gamma.\mathrm{dsc.cc}$, we can apply the formation rule for the discrete type to learn that $\Gamma.\mathrm{dsc} \gg \mathrm{Disc}(A) \text{ type @ par}$. Similarly, we use $\Gamma.\mathrm{dsc.cc} \gg t \in A \text{ @ pt}$ and $\Gamma.\mathrm{dsc.cc} \gg f \in A \text{ @ pt}$ to derive $\Gamma.\mathrm{dsc} \gg \mathrm{mod}(t) \in \mathrm{Disc}(A) \text{ @ par}$ and $\Gamma.\mathrm{dsc} \gg \mathrm{mod}(f) \in \mathrm{Disc}(A) \text{ @ par}$. Applying $\mathrm{unmod}(c)$ at these arguments gives $\Gamma.\mathrm{dsc} \gg \mathrm{unmod}(c)\,(\mathrm{Disc}(A))\,(\mathrm{mod}(t))\,(\mathrm{mod}(f)) \in \mathrm{Disc}(A) \text{ @ par}$ as required. $\square$

In particular, if we take the “shadows” of the canonical parametric elements $\mathfrak{t}, \mathfrak{f} \in \mathbb{B} \text{ @ par}$, we obtain their pointwise equivalents.

**Lemma 15.2.2.** We have the following equations.

$$\mathrm{shadow}\,(\mathrm{mod}(\mathfrak{t})) = \mathfrak{t} \in \mathbb{B} \text{ @ pt} \qquad \mathrm{shadow}\,(\mathrm{mod}(\mathfrak{f})) = \mathfrak{f} \in \mathbb{B} \text{ @ pt}$$

*Proof.* By the reduction equation for undisc. $\square$

Using the action of unmod on paths, we can then say that the shadow of any parametric Church boolean is equal to one of the canonical pointwise elements.

**Theorem 15.2.3.** For any $c : \mathrm{Glo}(\mathbb{B})$, we have either a path $(\mathrm{shadow}\,c) \rightsquigarrow \mathfrak{t}$ or a path $(\mathrm{shadow}\,c) \rightsquigarrow \mathfrak{f}$.