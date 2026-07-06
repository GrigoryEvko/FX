which corresponds to the 4 axiom, then in the logic we will be able to prove the implication

$$\langle \Box \mid \varphi \rangle \rightarrow \langle \Box^2 \mid \varphi \rangle \circledast$$

Combined with the equivalence $\langle \Box^2 \mid \varphi \rangle \leftrightarrow \langle \Box \mid \langle \Box \mid \varphi \rangle \rangle \circledast$ this implication enables a proof of a formula that looks like axiom 4 within the logic.

The addition of 4 to a modal logic may have far-reaching implications. For example, when combined with the $K$ axiom it allows us to prove the implication $\Box\Box A \rightarrow \Box\Box\Box A$. Thus, there should be a minimum amount of algebra on transformations that generates these consequences. To start, given three parallel modalities $\mu, \nu, \xi : n \rightarrow m$ and a formula $\varphi \circledast n$, the desired *hypothetical syllogism*

$$\frac{\langle \mu \mid \varphi \rangle \rightarrow \langle \nu \mid \varphi \rangle \circledast m \quad \langle \nu \mid \varphi \rangle \rightarrow \langle \xi \mid \varphi \rangle \circledast m}{\langle \mu \mid \varphi \rangle \rightarrow \langle \xi \mid \varphi \rangle \circledast m}$$

can be indirectly encoded by the existence of a composition operation on transformations: if $\alpha : \mu \Rightarrow \nu$ and $\beta : \nu \Rightarrow \xi$ then there should exist a composite transformation

$$\beta \circ \alpha : \mu \Rightarrow \xi$$

subject to associativity. There should also be an identity transformation $1_\mu : \mu \Rightarrow \mu$ for every modality $\mu : n \rightarrow m$. Note that we abuse the notations for composition and identities, using them for both modalities and their transformations.

This *vertical composition* of transformations is not sufficient to construct $\Box\Box\varphi \rightarrow \Box\Box\Box\varphi$ from the 4 axiom $\Box\varphi \rightarrow \Box\Box\varphi$. What is needed instead is a form of *horizontal composition*. Suppose that we have four modalities $\mu, \nu : n \rightarrow m$ and $\theta, \xi : o \rightarrow n$, and transformations $\beta : \theta \Rightarrow \xi$ and $\alpha : \mu \Rightarrow \nu$. This can be illustrated pictorially as

$$\underbrace{\begin{array}{c} \theta \\ o \quad \beta \Downarrow \\ \xi \end{array}}_{\xi} n \underbrace{\begin{array}{c} \mu \\ \alpha \Downarrow \\ \nu \end{array}}_{\nu} m$$

The *horizontal composition* of the transformations $\alpha$ and $\beta$ is a transformation

$$\alpha * \beta : \mu \circ \theta \Rightarrow \nu \circ \xi$$

which transforms the composite modality $\mu \circ \theta$ to the composite modality $\nu \circ \xi$.

If one of the two transformations is the identity then the horizontal composites are

$$1_\mu * \beta : \mu \circ \theta \Rightarrow \mu \circ \xi \qquad \alpha * 1_\theta : \mu \circ \theta \Rightarrow \nu \circ \theta$$

This special case is sometimes called *whiskering*, because its pictorial representation resembles adding a cat's whisker to a transformation:

$$\underbrace{\begin{array}{c} \theta \\ o \quad \beta \Downarrow \\ \xi \end{array}}_{\xi} n \xrightarrow{\mu} m \qquad \qquad o \xrightarrow{\theta} n \underbrace{\begin{array}{c} \mu \\ \alpha \Downarrow \\ \nu \end{array}}_{\nu} m$$

5