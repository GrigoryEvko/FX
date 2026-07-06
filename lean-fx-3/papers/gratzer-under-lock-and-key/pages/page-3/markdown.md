This notation says that $\mu$ is a *modality from mode $n$ to mode $m$*. We are likely to call $m$ and $n$ the *boundary* of the modality.$^{1}$

One may wonder how modal operators may be combined. Indeed, standard treatments of modal logic define a *modality* to be a composite of modal operators, and demonstrate various ‘reduction laws’ that simplify such composites; see e.g. Hughes and Cresswell [HC96, §3]. In our case, if we have two modalities $\nu : o \rightarrow n$ and $\mu : n \rightarrow m$, and a formula $\varphi \circledcirc o$ we see that

$$\langle \mu \mid \langle \nu \mid \varphi \rangle \rangle \circledcirc m$$

In a more traditional system of modal logic we might have tried to prove that such a formula is equivalent to a simpler formula $\langle \xi \mid \varphi \rangle \circledcirc m$ for some modality $\xi : o \rightarrow m$. We will once more break with tradition by presuming that such a modality always exists. In other words, we will assume that for any two modalities $\nu : o \rightarrow n$ and $\mu : n \rightarrow m$ there exists a *composite modality* $\mu \circ \nu : o \rightarrow m$. The rules of our logic will eventually allow us to prove for any formula $\phi \circledcirc o$ a logical equivalence

$$\langle \mu \mid \langle \nu \mid \varphi \rangle \rangle \leftrightarrow \langle \mu \circ \nu \mid \varphi \rangle \circledcirc m$$

In order to ensure that the composition of modalities behaves well we must assume that it is governed by some algebraic laws. In particular, we will assume that it is *associative*: for any three composable modalities $\xi : p \rightarrow o$, $\nu : o \rightarrow n$, $\mu : n \rightarrow m$ we must have

$$(\mu \circ \nu) \circ \xi = \mu \circ (\nu \circ \xi) : p \rightarrow m$$

Thus, a string of modalities will compose to a unique result. Moreover, we will assume for each mode $m \in \mathcal{M}$ an *identity modality*

$$1_m : m \rightarrow m$$

which will be an identity element for the composition operator $\circ$, so that for each $\mu : \nu \rightarrow \mu$ it is the case that $1_m \circ \mu = \mu = \mu \circ 1_n$. We will later be able to prove a logical equivalence $\langle 1_m \mid \varphi \rangle \leftrightarrow \varphi \circledcirc m$ for any $\varphi \circledcirc m$.

Readers that have encountered category theory before will immediately recognise that we have assumed that $\mathcal{M}$ is not just a set, but a category. Between any two modes $m, n \in \mathcal{M}$ (the *objects* of the category) we are given a set $\operatorname{Hom}_{\mathcal{M}}(m, n)$ of modalities from $m$ to $n$ (the *morphisms* of the category with *source* $m$ and *target* $n$). Moreover, for any three modes $m, n, o \in \mathcal{M}$ we are given an indexed binary operation

$$\circ_{m,n,o} : \operatorname{Hom}_{\mathcal{M}}(n, m) \times \operatorname{Hom}_{\mathcal{M}}(o, n) \rightarrow \operatorname{Hom}_{\mathcal{M}}(o, m)$$

which is associative and has ‘indexed’ identity elements $1_m \in \operatorname{Hom}_{\mathcal{M}}(m, m)$. Thus, modes and modalities form a category, i.e. a ‘typed’ monoid, whose elements (morphisms) have a ‘source’ and ‘target’ type, and where monoid multiplication (composition) can only happen when these types align. The structure of a category underlies a large part of

$^{1}$This term has its origins in higher category theory.

3