248

Cohesive parametric type theory

Corollary 14.3.6 (Modalities on extended substitutions). Given $\Upsilon \gg \gamma = \gamma' \in \Gamma \circledast n$ and $\mu : m \to n$, we have $\Upsilon.\mu \gg (\gamma : \Gamma) \otimes \mu = (\gamma' : \Gamma) \otimes \mu \in \Gamma.\mu \circledast m$.

Proof. By induction on $\Upsilon \gg \gamma = \gamma' \in \Gamma \circledast n$, applying Lemma 14.3.5 in the modal hypothesis case. $\square$

We have an analogous lemma for the action of interval restriction.

Lemma 14.3.7 (Restriction on extended substitutions). Given $\Upsilon \gg \gamma = \gamma' \in \Gamma \circledast$ par and any $\Gamma \gg r = r' \in \Gamma \circledast$ par, we have $\Upsilon \setminus r\gamma \gg (\gamma : \Gamma) \setminus r = (\gamma' : \Gamma') \setminus r' \in \Gamma \setminus r \circledast$ par.

Proof. If $\Gamma \gg r = s \in \Gamma \circledast$ par for some $\Gamma \gg s \in 2 \circledast$ par, then the result is trivial. If not, we proceed by induction on $\Upsilon \gg \gamma = \gamma' \in \Gamma \circledast$ par.

- Case: $\Upsilon \gg \cdot = \cdot \in \cdot \circledast$ par. Immediate.

- Case: $\Upsilon \gg (\gamma, M/a) = (\gamma', M'/a) \in (\Gamma, (\mu \mid a : A)) \circledast$ par.

- Case: $\mu = (\text{cc}, \mu')$. By assumption, $\Upsilon \gg \gamma = \gamma' \in \Gamma \circledast$ par. We can conclude $\Gamma \gg r = r' \in \Gamma \circledast$ par from $\Gamma, (\mu \mid a : A) \gg r = r' \in \Gamma \circledast$ par. Thus $\Upsilon \setminus r\gamma \gg (\gamma : \Gamma) \setminus r = (\gamma' : \Gamma) \setminus r' \in \Gamma \setminus r \circledast$ par by induction hypothesis. We moreover have $\Upsilon.\text{cc}.\mu' \gg M = M' \in A\gamma \circledast m$, and we know that $\Upsilon.\text{cc}.\mu' = \Upsilon \setminus r\gamma.\text{cc}.\mu'$.

- Case: $\mu = \cdot$ or $\mu = (\text{glo}, \mu')$. Immediate by induction hypothesis.

- Case: $\Upsilon \gg (\gamma, s/x) = (\gamma', s/x) \in (\Gamma, x : \mathbb{I}) \circledast$ par. By induction hypothesis and the substitution formation rule.

- Case: $\Upsilon \gg (\gamma, s/x) = (\gamma', s/x) \in (\Gamma, x : 2) \circledast$ par. As $r$ is not identified with an endpoint, we know that $r \neq x$. It follows that $\Gamma \gg r = r' \in \Gamma \circledast$ par. By induction hypothesis we then have $\Upsilon \setminus r\gamma \gg (\gamma : \Gamma) \setminus r = (\gamma' : \Gamma') \setminus r' \in \Gamma \setminus r \circledast$ par. As $\Upsilon \gg s \in 2 \circledast$ par, we also have $\Upsilon \setminus r\gamma \gg s \in 2 \circledast$ par.

- Case: $\Upsilon \gg (\gamma, s/x) = (\gamma', s/x) \in (\Gamma, x : \mathbb{I}) \circledast$ par.

- Case: $r = x$.

By the assumptions of this case, we have $\Upsilon \setminus r \gg \gamma = \gamma' \in \Gamma \circledast$ par as required.

- Case: $r \neq x$.

Then $\Gamma \gg r \in \Gamma \circledast$ par. By induction hypothesis we get $\Upsilon \setminus s \setminus r\gamma \gg (\gamma : \Gamma) \setminus r = (\gamma' : \Gamma') \setminus r' \in \Gamma \setminus r \circledast$ par, and we can see that $\Upsilon \setminus s \setminus r\gamma = \Upsilon \setminus r\gamma \setminus s$.

- Case: $\Upsilon \gg \gamma = \gamma' \in (\Gamma, \xi) \circledast m$. By induction hypothesis and the substitution formation rule. As $r$ is not identified with an endpoint, we know that $\xi$ does not mention $r$. $\square$