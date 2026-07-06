Related work 291

are much more recent [PR15; Shu18; GSB19; Zwa19; BCMEPS20], as the more complex structure of a dependent context naturally complicates the treatment of modalities. Similar issues arise in efforts to define dependent *substructural* type theories [CP02; Vák14; KPB15], which, like modal type theories, place restrictions on how variables can be accessed from the context.

Fortunately for us, frameworks for defining modal type theories have recently begun to crop up. Licata and Shulman [LS16] introduced the concept of a *mode theory*, a 2-category with modes as objects, modalities as morphisms, and maps between modalities as 2-cells, as a way of specifying a system of modalities. Their work builds on that of Reed [Ree09], who considers the special case of preorder mode theories. The generalization was motivated in particular by cohesive type theory, which requires the two parallel modalities cc, glo : pt → par. We use such a mode theory in the specification of our formalism in Chapter 16. Licata, Shulman, and Riley [LSR17] further generalize the Licata-Shulman framework to capture substructural phenomena.

The mode theory machinery was picked up by Gratzer, Kavvos, Nuyts, and Birkedal [GKNB20] in their *multimodal type theory* (**MTT**), a framework for *dependent* modal type theories. While our theory takes advantage of various simplifications appropriate to our special case, **MTT** has been tremendously useful as a template. Our formulation of modal hypotheses in particular is taken directly from **MTT**.

Our eliminator for discrete types is a restricted version of the **MTT** eliminator, which would additionally permit the principal argument ($P$ below) to be supplied beneath an auxiliary modality.

$$
\begin{aligned}
&\text{MTT-ELIM} \\
&\nu : \text{par} \rightarrow m \quad \Gamma.\nu.\text{cc} \gg A \text{ type @ pt} \quad \Gamma, (\nu \mid d : \text{Disc}(A)) \gg B \text{ type @ } m \\
&\Gamma.\nu \gg P \in \text{Disc}(A) \text{ @ par} \quad \Gamma, (\nu, \text{cc} \mid a : A) \gg N \in B[\text{mod}(a)/d] \text{ @ } m \\
&\hline
&\Gamma \gg \text{letdisc}_\nu(d.B, P, a.N) \in B[P/d] \text{ @ } m
\end{aligned}
$$

This parameter is necessary in general to take advantage of interactions between cc and other modalities; note how $\nu$ and cc are combined in the hypotheses of $N$. In the particular case of cohesion, however, the only essential property of modalities of the form $(\nu, \text{cc})$ is the equation $\Gamma.(\text{dsc}, \text{cc}) = \Gamma$, and the $\nu = \text{dsc}$ instance of the **MTT** eliminator is *derivable* (Lemma 15.1.1) by use of the codiscrete type. (A similar derivability was observed by Shulman for $b$-types [Shu18, Lemma 5.1].) This is fortunate, as the general rule would seriously complicate the computational interpretation. Consider that when the ambient context is an interval context $\Psi$, the principal argument $P$ is typed in context $\Psi.\nu$. This may not be an interval context: if $\Psi = (x : I)$ and $\nu = (\text{glo}, \text{dsc})$, for example, then we have $\Psi.\nu = (x : 2)$. We would therefore need to be able to evaluate terms in *extended* interval contexts (possibly containing endpoints). We conjecture that a system could be designed in which endpoint hypotheses can appear in genuine interval contexts and split becomes a sheaf condition imposed on types, but our approach seems much simpler.