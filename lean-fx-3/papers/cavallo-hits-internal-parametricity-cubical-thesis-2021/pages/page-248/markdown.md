236

Cohesive parametric type theory

Note in particular that substitutions from $\Gamma'$ into $(cc \mid a : A)$ correspond to substitutions from $\Gamma'.cc$ into $A$. Thus $(cc \mid a : -)$ represents the right adjoint to $-.cc$, which is to say the discrete embedding.

We may now formulate an elimination rule for $\text{Disc}(A)$ as suggested above.

$$\begin{array}{c} \Gamma.cc \gg A \text{ type @ pt} \quad \Gamma, d : \text{Disc}(A) \gg B \text{ type @ par} \\ \Gamma \gg P \in \text{Disc}(A) \text{ @ par} \quad \Gamma, (cc \mid a : A) \gg N \in B[\text{mod}(a)/d] \text{ @ par} \\ \hline \Gamma \gg \text{letdisc}(d.B, P, a.N) \in B[P/d] \text{ @ par} \end{array}$$

**Modal hypotheses and context operators** It is useful to more generally allow modal hypotheses under arbitrary compound modalities, sequences $\mu = (\mu_1, \ldots, \mu_n)$ where each $\mu_i$ is one of cc, dsc, or glo. Here we follow Gratzer, Kavvos, Nuyts, and Birkedal's **MTT** framework for modal type theories [GKNB20]. This is not only convenient in practice, but also gives us a way to define the right adjoint modal context operators ($.dsc$ and $-.glo$) on term hypotheses.

$$\begin{array}{l} (\Gamma, (\mu \mid a : A)).dsc := \Gamma.dsc, (cc, \mu \mid a : A) \\ (\Gamma, (\mu \mid a : A)).glo := \Gamma.glo, (dsc, \mu \mid a : A) \end{array}$$

Recall that a modal hypothesis over cc can be thought of as a hypothesis of discrete type. Thus we apply $-.dsc$ to a modal term hypothesis by adding cc to its modality. By the same token, a modal hypothesis over dsc corresponds to a hypothesis of global section type. Thus we define these operators by what Nuyts, Vezzosi, and Devriese call *left division* [NVD17], that is, by adjusting the modality of each hypothesis.

The leftmost adjoint again demands special treatment. To apply the connected components modality to a hypothesis, we check if it is already typed under the connected components modality. If so, the context application cancels the hypothesis modality. Other hypotheses are simply thrown away; there is no way to access an ordinary term hypothesis beneath $-.cc$.

$$(\Gamma, (\mu \mid a : A)).cc := \left\{ \begin{array}{ll} \Gamma.cc, (\mu' \mid a : A), & \text{if } \mu = cc, \mu' \\ \Gamma.cc, & \text{otherwise} \end{array} \right.$$

Again, it is instructive to draw a parallel with interval restriction. The restriction $- \setminus x$ deletes term hypotheses that succeed $x$ in the context, as these could be instantiated with terms that use $x$. Likewise, $-.cc$ deletes hypotheses that could use *any* bridge interval variable, which is to say all hypotheses except those hidden behind cc.

Many of the complications of the theory developed below have their root in modal hypotheses. For example, to check that $-.glo$ takes well-formed contexts to well-formed contexts, we must first know that $\Gamma.\mu \gg A$ pretype implies $\Gamma.\mu.glo.dsc \gg A$ pretype. Thus careful staging is required.