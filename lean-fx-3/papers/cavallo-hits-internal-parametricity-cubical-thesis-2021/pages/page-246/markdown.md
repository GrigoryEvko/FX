234*Cohesive parametric type theory*

We define each of these by recursion on the raw context $\Gamma$; we then must show that each modal operator takes well-typed contexts (those satisfying $\Gamma \operatorname{ctx} @ m$) to well-formed contexts.

One wrinkle appears when we try to define the global sections of the context $(x : I)$. The bridge interval is meant to have two global sections, namely the endpoints 0 and 1. To express this, we introduce a new form of *endpoint hypothesis* that ranges over the two constants.

$$
\frac{\Gamma \operatorname{ctx} @ m}{(\Gamma, x : 2) \operatorname{ctx} @ m}
$$

We can then define $(\Gamma, x : I).\operatorname{glo} := \Gamma.\operatorname{glo}, x : 2$. One unfortunate consequence of this definition is that $-.\operatorname{glo}$ does not restrict to an operator on interval contexts: $(x : I)$ is an interval context but $(x : I).\operatorname{glo} = (x : 2)$ is not. This is a source of friction when we develop the theory of closing substitutions.

Aside from this exception, the behaviors of the context operators on interval hypotheses are straightforward. The connected components operator deletes bridge interval hypotheses, in effect collapsing them: the bridge interval has a single connected component.

$$
(\Gamma, x : I).\operatorname{cc} := \Gamma.\operatorname{cc}
$$

It is useful to think of $-.\operatorname{cc}$ as having a similar character to the interval restriction operator $- \setminus x$: where restriction deletes a single bridge interval variable $x$, $\operatorname{cc}$ deletes *all* bridge interval variables. The discrete embedding $-.\operatorname{dsc}$ is not defined on bridge interval hypotheses, as these only appear in parametric contexts. Each operator commutes with path interval and endpoint hypotheses.

A final question that needs answering is how to define the action of modalities on *term* hypotheses; this we defer for the moment.

**Negative elimination** We take two different approaches to elimination: one for the global type $\operatorname{Glo}(A)$ and codiscrete type $\operatorname{Codisc}(A)$, one for the discrete type $\operatorname{Disc}(A)$. The former two have additional structure we can exploit to give simple projection rules: not only are they right adjoints, but their left adjoints are themselves right adjoints. Taking $\operatorname{Glo}(A)$ as our example, we are able to give the following projection, reduction, and