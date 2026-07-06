Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:17

Unlike path variables, however, we will only have weakening and exchange for the bridge interval: the contraction principle fails. The bridge interval is thus substructural, in particular affine.

The lack of contraction means that we cannot always apply a bridge variable substitution $-[\boldsymbol{y}/\boldsymbol{x}]$ to a term $M$: if $M$ already mentions $\boldsymbol{y}$, this amounts to contracting $\boldsymbol{y}$ and $\boldsymbol{x}$. What we have is fresh substitution: we can substitute a variable $\boldsymbol{y}$ for $\boldsymbol{x}$ in $M$ when $\boldsymbol{y}$ does not occur in $M$ (i.e., is apart from $M$). To formulate fresh substitution for open terms, we define the following context restriction operation, roughly following Cheney's approach to nominal type theory [Che12]. Intuitively, given a context $\Gamma$ and interval term $\boldsymbol{r}$ in that context, $\Gamma\backslash\boldsymbol{r}$ is the part of $\Gamma$ guaranteed to be apart from $\boldsymbol{r}$: when $\boldsymbol{r}$ is a variable $\boldsymbol{x}$, it includes all other bridge variables, all path variables, constraints that do not involve $\boldsymbol{r}$, and those term variables that are introduced before $\boldsymbol{r}$. The constants $\mathbf{0}$ and $\mathbf{1}$ are considered to be apart from everything. That is, we define $\Gamma\backslash\boldsymbol{r} := \Gamma$ when $\Gamma \gg \boldsymbol{r} = \boldsymbol{\varepsilon} \in \mathbf{I}$ for some $\boldsymbol{\varepsilon} \in \{\mathbf{0}, \mathbf{1}\}$ and as follows otherwise.

$$(\Gamma, y : \mathbb{I})\backslash\boldsymbol{x} := \Gamma\backslash\boldsymbol{x}, y : \mathbb{I}$$

$$(\Gamma, a : A)\backslash\boldsymbol{x} := \Gamma\backslash\boldsymbol{x}$$

$$(\Gamma, \boldsymbol{y} : \mathbf{I})\backslash\boldsymbol{x} := \begin{cases} \Gamma & \text{if } \boldsymbol{x} = \boldsymbol{y} \\ \Gamma\backslash\boldsymbol{x}, \boldsymbol{y} : \mathbf{I} & \text{if } \boldsymbol{x} \neq \boldsymbol{y} \end{cases}$$

$$(\Gamma, \xi)\backslash\boldsymbol{x} := \begin{cases} \Gamma\backslash\boldsymbol{x} & \text{if } \boldsymbol{x} \text{ occurs in } \xi \\ \Gamma\backslash\boldsymbol{x}, \xi & \text{otherwise} \end{cases}$$

We then have the following rule for extending a substitution by a bridge interval term.

$$\frac{\begin{array}{c} \text{I-SUBST} \\ \Gamma' \gg \boldsymbol{r} \in \mathbf{I} \quad \Gamma'\backslash\boldsymbol{r} \gg \gamma \in \Gamma \\ \hline \Gamma' \gg (\gamma, \boldsymbol{r}/\boldsymbol{x}) \in \Gamma \end{array}}{}$$

The restriction in the premises prevents us from deriving, in particular, the following contraction or "diagonal" substitution, which attempts to substitute the same bridge variable $\boldsymbol{x}$ for two distinct variables $\boldsymbol{y}$ and $\boldsymbol{z}$.

$$\boldsymbol{x} : \mathbf{I} \gg (\boldsymbol{x}/\boldsymbol{y}, \boldsymbol{x}/\boldsymbol{z}) \in (\boldsymbol{y} : \mathbf{I}, \boldsymbol{z} : \mathbf{I}) \quad \times$$

When working with a context of the form $(\Gamma, \boldsymbol{x} : \mathbf{I}, \Gamma')$, we therefore think of the variables in $\Gamma$ as being apart from $\boldsymbol{x}$: we are disallowed from substituting a term that mentions $\boldsymbol{x}$ for a variable in $\Gamma$: in a substitution. On the other hand, we can substitute terms that mention $\boldsymbol{x}$ for variables in $\Gamma'$. In accordance with this intuition, we can exchange term variables past bridge variables in one direction but not the other, as witnessed by the following substitution.

$$a : A, \boldsymbol{x} : \mathbf{I} \gg (\boldsymbol{x}/\boldsymbol{x}, a/a) \in (\boldsymbol{x} : \mathbf{I}, a : A)$$

In the domain of this substitution, $a : A$ ranges over fewer terms: only those elements of $A$ that are apart from $\boldsymbol{x}$.

In keeping with the lack of contraction, we allow constraints only to identify bridge variables with constants, not with other variables.

$$\frac{\begin{array}{c} \text{I-CONSTRAINT} \\ \Gamma \gg \boldsymbol{r} \in \mathbf{I} \quad \varepsilon \in \{0, 1\} \\ \hline \Gamma \gg \boldsymbol{r} = \varepsilon \text{ constraint} \end{array}}{}$$

We note that affine variables are also central to nominal sets [Pit13], where they are used to represent variable names in syntax. The BCH model of univalent type theory in