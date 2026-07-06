4

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

1.2. Equivalences and bi-equivalences in an $\omega$-category. The following is originally due to Métayer, and is also considered in [AL20, §1.2] (under the terminology of structure of reversibility) and [Lou23, Définition 1.1.7] (under the terminology of ensemble d'inversibilité).

Definition 1.2. Let $\mathcal{D}$ be an $\omega$-category. An invertibility set in $\mathcal{D}$ is a set $E = \coprod_{n>0} E_n$ with $E_n \subseteq \mathcal{D}_n$ such that, for all $n > 0$ and $a \in E_n$, there exists $\tilde{a} \in E_n$ of the form

$$\tilde{a} \colon d_{n-1}^+ a \to d_{n-1}^- a$$

and $c, c' \in E_{n+1}$ of the form

$$c \colon \tilde{a} \underset{n-1}{*} a \to \mathrm{id}_{d_{n-1}^- a} \quad \text{and} \quad c' \colon a \underset{n-1}{*} \tilde{a} \to \mathrm{id}_{d_{n-1}^+ a}.$$

In the situation above we say that $\tilde{a}$ is a weak inverse for $a$.

Definition 1.3. Let $\mathcal{D}$ be an $\omega$-category and $n > 0$. Given $a \in \mathcal{D}_n$, the $n$-cell $a$ is said to be an $\omega$-equivalence if there exists an invertibility set $E$ such that $a \in E$. We denote by $\mathrm{eq}_n \mathcal{D}$ the set of all $n$-cells in $\mathcal{D}$ that are $\omega$-equivalences and by $\mathrm{eq} \mathcal{D} := \coprod_{n>0} \mathrm{eq}_n \mathcal{D}$ the set of all $\omega$-equivalences in $\mathcal{D}$.

The following is from [AL20, §1.2] and [Lou23, Lemme 1.1.8], and is generally taken as the defining property for the set $\mathrm{eq} \mathcal{D}$ of $\omega$-equivalences in an $\omega$-category $\mathcal{D}$ (see e.g. [LMW10, Definition 6]).

Proposition 1.4. Let $\mathcal{D}$ be an $\omega$-category and $n > 0$. Given $a \in \mathcal{D}_n$, we have that $a \in \mathrm{eq}_n \mathcal{D}$ if and only if there exist $\tilde{a} \in \mathcal{D}_n$ of the form

$$\tilde{a} \colon d_{n-1}^+ a \to d_{n-1}^- a$$

and $c, c' \in \mathrm{eq}_{n+1} \mathcal{D}$ of the form

$$c \colon \tilde{a} \underset{n-1}{*} a \to \mathrm{id}_{d_{n-1}^- a} \quad \text{and} \quad c' \colon a \underset{n-1}{*} \tilde{a} \to \mathrm{id}_{d_{n-1}^+ a}.$$

Remark 1.5. Given an $\omega$-category $\mathcal{D}$, by Proposition 1.4 the set $\mathrm{eq} \mathcal{D}$ is the maximal invertibility set in $\mathcal{D}$.

Definition 1.6. Let $\mathcal{D}$ be an $\omega$-category. A bi-invertibility set in $\mathcal{D}$ is a set $E = \coprod_{n>0} E_n$ with $E_n \subseteq \mathcal{D}_n$ such that, for all $n > 0$ and $a \in E_n$, there exist $a^L, a^R \in \mathcal{D}_n$ of the form

$$a^L, a^R \colon d_{n-1}^+ a \to d_{n-1}^- a$$

and $c, c' \in E_{n+1}$ of the form

$$c \colon a^L \underset{n-1}{*} a \to \mathrm{id}_{d_{n-1}^- a} \quad \text{and} \quad c' \colon a \underset{n-1}{*} a^R \to \mathrm{id}_{d_{n-1}^+ a}.$$

In the situation above, we say that $a^L$, resp. $a^R$, is a left inverse, resp. right inverse, for $a$.

Definition 1.7. Given an $\omega$-category $\mathcal{D}$ and $a \in \mathcal{D}_n$ with $n > 0$, the $n$-cell $a$ is said to be an $\omega$-bi-equivalence if there exists a bi-invertibility set $E$ such that $a \in E$. We denote by $\mathrm{bieq}_n \mathcal{D}$ the set of all $n$-cells in $\mathcal{D}$ that are $\omega$-bi-equivalences and by $\mathrm{bieq} \mathcal{D} := \coprod_{n>0} \mathrm{bieq}_n \mathcal{D}$ the set of all $\omega$-bi-equivalences in $\mathcal{D}$.

Remark 1.8. If $E$ is an invertibility set in an $\omega$-category $\mathcal{D}$, then $E$ is also a bi-invertibility set in $\mathcal{D}$.

The following is often taken as the defining property for the set $\mathrm{bieq} \mathcal{D}$ of $\omega$-bi-equivalences in an $\omega$-category $\mathcal{D}$ (cf. in [Ric20, Définition 4]).