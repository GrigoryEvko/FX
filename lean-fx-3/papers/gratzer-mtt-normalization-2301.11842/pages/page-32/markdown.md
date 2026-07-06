27:32

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

$$\left\{ \begin{array}{l l} \mathsf {J} (z, B, b, a _ {0}, a _ {1}, p) & \operatorname {p r f} = \iota_ {1} (z) \\ \downarrow \mathbf {J} (\lambda l, r, p. B (\uparrow l, \uparrow r, \uparrow p). \mathsf {c o d e}, \lambda a. \downarrow b (\uparrow a), e) & \operatorname {p r f} = \iota_ {2} (\iota_ {1} (e, -)) \\ b (a _ {0}) & q = \iota_ {2} (\iota_ {2} (-, -, -)) \end{array} \right.$$

Lemma 5.11. $(\mathsf{Ty}_m^*, \mathsf{Tm}_m^*)$ is closed under a universe and the relevant constants lie over their counterparts in $(\mathsf{Ty}_m, \mathsf{Tm}_m)$.

Proof. We begin by constructing the two constants for the universe and the decoding family:

$$\begin{array}{l} \operatorname{Uni} ^ {*}: \left\{\mathrm{Ty} _ {m} ^ {*} \mid z: \mathbf{syn} \mapsto \operatorname{Uni} \right\} \\ \operatorname{El} ^ {*}: (A: \operatorname{Tm} _ {m} ^ {*} (\operatorname{Uni} ^ {*})) \rightarrow \left\{\operatorname{Ty} _ {m} ^ {*} \mid z: \mathbf{syn} \mapsto \operatorname{El} (A) \right\} \\ \end{array}$$

At this point we take advantage of the fact that pred is an element of $U_1$; in particular, we observe that $U_0$ is small enough to fit inside $U_1$.

We may then define $\Psi$ by realigning the following element of $U_1$ along the evident isomorphism to $\mathsf{Tm}_m^*(z, \mathsf{Uni}(z))$:

$$\begin{array}{l} \text {record} \Psi : \left\{\mathrm{U} _ {1} \mid z: \mathbf {s y n} \mapsto \mathrm{Tm} _ {m} ^ {*} (z, \mathrm{Uni}) \right\} \text {where} \\ \text {code}: \mathrm{Nf} _ {m} (\mathrm{Uni}) \\ \text {pred}: \left\{\mathrm{U} _ {0} \mid z: \mathbf {s y n} \mapsto \mathrm{Tm} _ {m} (z, \mathrm{El} (\text {code})) \right\} \\ \text {reflect}: \left\{\mathrm{Ne} _ {m} (\mathrm{El} (\text {code})) \rightarrow \text {pred} \mid z: \mathbf {s y n} \mapsto \mathrm{id} \right\} \\ \text {reify}: \left\{\text {pred} \rightarrow \mathrm{Nf} _ {m} (\mathrm{El} (\text {code})) \mid z: \mathbf {s y n} \mapsto \mathrm{id} \right\} \\ \end{array}$$

With $\Psi$ in hand, we may define Uni*:

$$\begin{array}{l} \operatorname{Uni} ^ {*}. \text {code} = \operatorname{Uni} \\ \operatorname{Uni} ^ {*}. \text {pred} = \Psi \\ \operatorname{Uni} ^ {*}. \text {reflect} = \lambda e. \langle \mathbf {u p} (e); \mathrm{Ne} _ {m} (\mathrm{El} (e)); \mathrm{id}; \lambda e. \mathbf {u p} (e) \rangle \\ \operatorname{Uni} ^ {*}. \text {reify} = \lambda A. A. \text {code} \\ \end{array}$$

The definition of $\mathsf{El}^*$ is essentially cumulativity:

$$\operatorname{El} ^ {*} (\langle \text {code}; \text {pred}; \text {reify}; \text {reflect} \rangle) = \langle \operatorname{El} (\text {code}); \text {pred}; \text {reify}; \text {reflect} \rangle$$

It remains to show that $(\mathsf{Uni}^*, \mathsf{El}^*)$ is closed under various type formers. We show a representative cases: modal types. This concretely entails implementing the following constants:

$$\begin{array}{l} \widehat {\operatorname{Mod}} ^ {*}: (\mu \mid A: \operatorname{Tm} _ {n} ^ {*} (\operatorname{Uni} ^ {*})) \rightarrow \left\{\operatorname{Tm} _ {m} ^ {*} (\operatorname{Uni} ^ {*}) \mid z: \mathbf {s y n} \mapsto \widehat {\operatorname{Mod}} (z, A) \right\} \\ \operatorname{dec} _ {\widehat {\operatorname{Mod}}} ^ {*}: (\mu \mid A: \operatorname{Tm} _ {n} ^ {*} (\operatorname{Uni} ^ {*})) \\ \rightarrow \left\{\mathrm{Tm} _ {m} ^ {*} \left(\mathrm{El} ^ {*} \left(\widehat {\operatorname{Mod}} ^ {*} (A)\right)\right) \cong \mathrm{Tm} _ {m} ^ {*} \left(\operatorname{Mod} _ {\mu} ^ {*} \left(\mathrm{El} ^ {*} (A)\right)\right) \mid z: \mathbf {s y n} \mapsto \operatorname{dec} _ {\widehat {\operatorname{Mod}}} (z, A) \right\} \\ \end{array}$$

Fix $(\mu \mid A: \mathsf{Tm}_n^*(\mathsf{Uni}^*))$. We realign $\mathsf{Tm}_m^*(\mathsf{Mod}_\mu^*(\mathsf{El}^*(A)))$ along the isomorphism $\mathsf{dec}_{\widehat{\mathsf{Mod}}}$ to obtain a type $\Psi$ and an isomorphism:

$$\operatorname{dec} _ {\operatorname{Mod} _ {\mu}} ^ {*}: \left\{\Psi \cong \operatorname{Tm} _ {m} ^ {*} \left(\operatorname{Mod} _ {\mu} ^ {*} \left(\operatorname{El} ^ {*} (A)\right)\right) \mid z: \mathbf {s y n} \mapsto \operatorname{dec} _ {\widehat {\operatorname{Mod}}} (z, A) \right\}$$

It remains only to define $\widehat{\mathsf{Mod}}^*(A)$ such that $\widehat{\mathsf{Mod}}^*(A).\mathsf{pred} = \Psi$:

$$\begin{array}{l} \widehat {\operatorname{Mod}} ^ {*} (A). \text {code} = \langle \mu \mid \widehat {A . \text {code}} \rangle \\ \widehat {\operatorname{Mod}} ^ {*} (A). \text {pred} = \Psi \\ \widehat {\operatorname{Mod}} ^ {*} (A). \text {reflect} = \lambda e. (\operatorname{dec} _ {\widehat {\operatorname{Mod}}} ^ {*}) ^ {- 1} (\uparrow_ {\operatorname{Mod} _ {\mu} ^ {*} (\operatorname{El} ^ {*} (A))} \operatorname{dec} ^ {\triangleright} (e)) \\ \end{array}$$