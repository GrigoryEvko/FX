Just as with ordinary contexts, we regard these rules as generating telescopes 'inductively', although this is not formally the case syntactically. We thus regard some other operation on telescopes as 'defined' when we specify rules for how it computes on these forms. This is justified in most models, where we do actually define the judgment of telescopes inductively by the above rules.

For example, the premise of the second rule above requires knowing how to extend a context by a telescope. We write this with a distinctive notation as $\Gamma \mid \Theta$, from which the reader can infer that $\Theta$ is a telescope. Since $\mid$ is an operation on contexts, not a constructor of contexts, it computes on the constructors of telescopes:

$$\frac{\Gamma \vdash_p \Theta \text{tel}_\ell}{(\Gamma \mid \Theta) \text{ctx}} \quad (\Gamma \mid ()_p) \equiv \Gamma \quad (\Gamma \mid (\Theta, x :^\mu A)) \equiv ((\Gamma \mid \Theta), x :^\mu A)$$

We consider the operation $\mid$ to be left-associative with the comma. Thus, for instance, the context $\Gamma \mid \Theta$, $\bullet_\mu$ in the rule for extending a telescope by a type means $(\Gamma \mid \Theta)$, $\bullet_\mu$.

By a strict telescope we mean a telescope without any nontrivially modal variables.

$$\frac{\Gamma \text{ctx}_p}{\Gamma \vdash_p ()_p \text{stel}_\ell} \quad \frac{\Gamma \vdash_p \Theta \text{stel}_\ell \quad \Gamma \mid \Theta \vdash_p A \text{type}_{\ell'} \quad \ell' \leqslant \ell}{\Gamma \vdash_p (\Theta, x :^\mu A) \text{stel}_\ell}$$

As is evident, we do not distinguish syntactically between general telescopes and strict ones. That is, we consider strictness to be a mere property of a telescope, or alternatively we treat the obvious map from strict telescopes to telescopes as an implicit coercion.

Similarly, we can introduce a 'lifting' operation taking a telescope to any higher level.

$$\frac{\Gamma \vdash_p \Theta \text{tel}_\ell \quad \ell \leqslant \ell'}{\Gamma \vdash_p \Theta \text{tel}_{\ell'}}$$

As is evident from the notation, we also treat this as an implicit coercion. Thus, when we define it recursively on the structure of a telescope, the rules look trivial unless we annotate them somehow with levels:

$$()_p \equiv ()_p \quad (\Theta, x :^\mu A) \equiv (\Theta, x :^\mu A) \quad \triangleleft$$

### 2.3.2 Partial substitutions

If $\Gamma \vdash \Upsilon \text{tel}_\ell$ there is a judgment $\Gamma \vdash \sigma : \Upsilon$ for the 'elements' of $\Upsilon$. We call such $\sigma$ a 'partial substitution', thinking of it as a substitution $\Gamma \Rightarrow (\Gamma \mid \Upsilon)$ that is the identity on $\Gamma$. Formally, we specify that they can be built out of terms:

$$\frac{\Gamma \vdash_q \sigma : \Upsilon \quad \Gamma \mid \Upsilon, \bullet_\mu \vdash_p A \text{type}_\ell \quad \Gamma, \bullet_\mu \vdash_p t : A [1_\Gamma \mid \sigma, \bullet_\mu]}{\Gamma \vdash_p [\sigma, t] : (\Upsilon, x :^\mu A)}$$

The second rule involves a notion of extending an ordinary substitution by a partial one.

$$\frac{\theta : \Gamma \Rightarrow_p \Delta \quad \Delta \vdash_p \Upsilon \text{tel}_\ell \quad \Gamma \vdash_p \sigma : \Upsilon [\theta]}{[\theta \mid \sigma] : \Gamma \Rightarrow_p (\Delta \mid \Upsilon)} \quad [\theta \mid []_p] \equiv \theta$$

$$[\theta \mid [\sigma, t]] \equiv [[\theta \mid \sigma], t]$$

17