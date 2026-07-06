11:12

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

to induce a morphism $\langle \mu \mid A \rangle \rightarrow A$ we include a unique non-trivial 2-cell $\epsilon : \mu \Rightarrow 1$. In order to ensure that this 2-cell to be unique, we add equations such as $\epsilon \star 1_\mu = 1_\mu \star \epsilon : \mu \circ \mu \Rightarrow \mu$, where $\star$ denotes the horizontal composition of 2-cells. The resulting mode theory is a 2-category, albeit a very simple one: it is in fact only a *poset-enriched* category.

We can show that $\langle \mu \mid A \rangle$ is a comonad by defining the expected operations using the combinators of Section 3.1:

$$\begin{aligned} \text{dup}_A : \langle \mu \mid A \rangle &\rightarrow \langle \mu \mid \langle \mu \mid A \rangle \rangle & \text{extract}_A : \langle \mu \mid A \rangle \rightarrow A^\epsilon \\ \text{dup}_A &\triangleq \text{comp}_{\mu,\mu}^{-1} & \text{extract}_A &\triangleq \text{triv}^{-1}(-) \circ \text{coe}[\epsilon : \mu \Rightarrow 1] \end{aligned}$$

We must also show that $\text{dup}_A$ and $\text{extract}_A$ satisfy the comonad laws, but that automatically follows from general facts pertaining to **coe** and **comp**.$^2$ This is indicative of the benefits of using MTT: every general result about it also applies to this instance, including the canonicity theorem of Section 5.

#### 4. ALGEBRAIC SYNTAX

Until this point we have presented a curated, high-level view of MTT, and we have avoided any discussion of its metatheory. Yet, syntactic matters can be quite complex, and have historically proven to be sticking points for modal type theory. While such details are not necessary for the casual reader, it is essential to validate that MTT is syntactically well-behaved, enjoying e.g. a substitution principle. The aim of this section is to provide a setting for this study: we introduce the formal counterpart of MTT, which is given as a *generalized algebraic theory* (GAT) [Car78, KKA19].

Historically, GATs were used in the semantics of type theory, but modern techniques show that they are also useful in the analysis of syntax. For example, recasting MTT as a GAT naturally leads us to include *explicit substitutions* [Cur90, ML92, Gra11] in the syntax. Thus, substitution in MTT is not a metatheoretic operation on raw terms, but a syntactic operation within the theory. This presentation helps us carefully state the equations that govern substitutions and their interaction with type formers. We consequently obtain an elegant *substitution calculus*, which can often be quite complex for modal type theories.

This approach proffers a number of technical advantages. Amongst other things, the theorems proven in the aforementioned works on GATs imply the following points:

1. (1) We absolve ourselves from having to prove tedious syntactic metatheorems, e.g. admissibility of substitution.
2. (2) We automatically obtain a notion of *model* of our theory, which is given in entirely algebraic terms.
3. (3) We obtain a notion of *homomorphism of models*. (NB that this notion is rather *strict* and not fit for every purpose.)
4. (4) In an equally automatic fashion, we obtain an *initial model* for the algebraic theory, which we consider as our main formal object of study.
5. (5) The unique morphism of models from this initial model to any other is the *semantic interpretation map*. We then have no need to explicitly describe these semantic maps and prove that they are well-defined on derivations, as done e.g. by [Hof97].

$^2$In particular, our modal combinators satisfy a variant of the *interchange law* of a 2-category.