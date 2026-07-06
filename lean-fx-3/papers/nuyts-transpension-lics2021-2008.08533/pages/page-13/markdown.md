Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:13

$$i \hat{c} = \text{unmer} \left( u.\text{case} \hat{c} u \text{ of} \left\{ \begin{array}{l} \text{inl } a \mapsto \text{mer}[u] (\text{inl } (\lambda u.a)) \\ \text{inr } b \mapsto \text{mer}[u] (\text{inr } (\lambda u.b)) \end{array} \right\} \right).$$

Let us consider our categorically motivated creation from a more type-theoretical perspective. We obtain an argument $\hat{c} : \forall u.A \uplus B$ which we would like to pattern match on, in order to create an element of type $(\forall u.A) \uplus (\forall u.B)$. Of course we cannot pattern match on a function, so we call the unmer constructor which brings $u : \mathbb{U}$ in scope and changes the goal to $\langle [u] ((\forall v.A[v/u]) \uplus (\forall v.B[v/u]))$. We can then reduce $\hat{c}$ by one dimension by applying it to $u$, allowing a case analysis. The first case brings in scope $a : A$ (and the second case will be analogous), so we are in context $(\Gamma, \hat{c} : \forall u.A \uplus B, u : \mathbb{U}, a : A)$. We then use the meridian constructor, which again removes $u$ from scope, turns $a : A$ into a function $\lambda u.a : \forall u.A$ and again reduces the goal to $(\forall u.A) \uplus (\forall u.B)$, so that inl completes the proof. We have essentially pattern matched on a higher-dimensional object!

Let us now check that $i$ is indeed inverse to the trivial implementation of $i^{-1}$. We have:

$$\begin{array}{l} (i \circ i^{-1})(\text{inl } \hat{a}) = i(\lambda u.\text{inl } (\hat{a} u)) \\ = \text{unmer}(u. (\text{mer}[u] (\text{inl } (\lambda u.a)))[u/u, \hat{a} u/a] ) \\ = \text{unmer}(u.(\text{mer}[u] (\text{inl } (\lambda u.a)[\lambda u.\hat{a} u/\lambda u.a] )))) \quad \text{(FF:TRANSP:INTRO:NAT)} \\ = \text{unmer}(u.(\text{mer}[u] (\text{inl } (\lambda u.\hat{a} u)))) \quad \text{(Corollary 2.3)} \\ = \text{inl } \hat{a}. \quad \text{(FF:TRANSP:BETA)} \end{array}$$

and similar for $(i \circ i^{-1})(\text{inr } \hat{b})$. Using the technique of higher dimensional pattern matching just developed, we can prove the other equation also by pattern matching! By similar steps as before, we have:

$$\begin{array}{l} (i^{-1} \circ i)(\lambda u.\text{inl } (\hat{a} u)) = i^{-1}(\text{unmer}(u. (\text{mer}[u] (\text{inl } (\lambda u.a)))[u/u, \hat{a} u/a] )) \\ = i^{-1}(\text{unmer}(u.(\text{mer}[u] (\text{inl } \hat{a})))) = i^{-1}(\text{inl } \hat{a}) = \lambda u.\text{inl } (\hat{a} u), \end{array}$$

and a similar result for $(i^{-1} \circ i)(\lambda u.\text{inr } (\hat{b} u))$.

### 3. MULTIMODE TYPE THEORY

As announced, we will rely on the extensional version of Gratzer et al.'s multimode and multimodal dependent type system MTT [GKNB21, GKNB20a] in order to frame the transpension and its left adjoints as modal operators. We refer to the original work for details, but give a brief overview in the current section. In Section 3.4, we decorate the usual MTT notation with reminders of the modalities' semantic left adjoints, which are syntactically obscured by the lock notation.

3.1. The mode theory. MTT is parametrized by a mode theory, which is a strict 2-category whose objects, morphisms and 2-cells we will refer to as modes, modalities and, well, 2-cells respectively. Semantically, every mode $p$ will correspond to an entire model of dependent type theory $[[p]]$. A modality $\mu : p \to q$ will consist of a functor $[[\widehat{\bullet}_\mu] : [[q]] \to [[p]]$ acting on contexts and substitutions, and an operation $[[\mu]]$ that is almost a dependent right adjoint (DRA [BCM$^{+}$20]) to $[[\widehat{\bullet}_\mu]]$; for all our purposes it will be an actual DRA and even one arising from a weak CwF morphism [BCM$^{+}$20, lemma 17][Nuy18a]. A 2-cell $\alpha : \mu \Rightarrow \nu$ is interpreted as a natural transformation $[[\widehat{\bullet}_\alpha] : [[\widehat{\bullet}_\nu]] \to [[\widehat{\bullet}_\mu]]$ and hence also gives rise to an appropriate transformation $[[\alpha] : [[\mu]] \to [[\nu]]$.