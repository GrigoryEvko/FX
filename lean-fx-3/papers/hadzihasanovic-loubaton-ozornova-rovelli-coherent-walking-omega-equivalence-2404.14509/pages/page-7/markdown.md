A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

7

We first consider $x, y \in \mathcal{D}_{n+1}$ defined as follows:

$$\begin{aligned} y: & a \begin{array}{cc} * & b^L \\ n-1 & n-1 \end{array} & b \begin{array}{cc} * & a^L \\ n-1 & n-1 \end{array} & a \begin{array}{cc} * & a^R \\ n-1 & n-1 \end{array} \xrightarrow{\text{id}_a \begin{array}{cc} * & c \\ n-1 & n-1 \end{array} \begin{array}{cc} * & \text{id}_a R \end{array}} & a \begin{array}{cc} * & a^R \\ n-1 & n-1 \end{array} \xrightarrow{c'} & \text{id}_{d_{n-1}^+} a \\ x: & a \begin{array}{cc} * & b^L \\ n-1 & n-1 \end{array} & b \begin{array}{cc} * & a^L \\ n-1 & n-1 \end{array} & a \begin{array}{cc} * & a^R \\ n-1 & n-1 \end{array} \xrightarrow{\text{id}_a \begin{array}{cc} * & b^L \\ n-1 & n-1 \end{array} \begin{array}{cc} * & a^L \\ n-1 & n-1 \end{array} \begin{array}{cc} * & c' \\ n-1 & n-1 \end{array}} & a \begin{array}{cc} * & b^L \\ n-1 & n-1 \end{array} \begin{array}{cc} * & a^L \\ n-1 & n-1 \end{array} \end{aligned}$$

By Propositions 1.11, 1.13 and 1.15, we know that $x, y \in \text{bieq}_{n+1} \mathcal{D}$. If $x^L$ denotes a left inverse for $x$, we then define $e^L := a \begin{array}{cc} * & n-1 \\ n-1 & b^L \end{array} \in \mathcal{D}_n$ and $e^R := a \begin{array}{cc} * & n-1 \\ n-1 & b^R \end{array} \in \mathcal{D}_n$, and set $\ell \in \mathcal{D}_{n+1}$ and $\ell' \in \mathcal{D}_{n+1}$ to be the composites

$$\begin{aligned} \ell: & e^L \begin{array}{cc} * & e \\ n-1 & \end{array} \xrightarrow{x^L} & a \begin{array}{cc} * & b^L \\ n-1 & \end{array} & b \begin{array}{cc} * & a^L \\ n-1 & \end{array} & a \begin{array}{cc} * & a \\ n-1 & \end{array} \xrightarrow{x} & a^R \xrightarrow{y} & \text{id}_{d_{n-1}^-} e \\ \ell': & e \begin{array}{cc} * & e \\ n-1 & \end{array} \xrightarrow{\text{id}_a \begin{array}{cc} * & c \\ n-1 & n-1 \end{array} \begin{array}{cc} * & \text{id}_a R \end{array}} & b \begin{array}{cc} * & d' \\ n-1 & \end{array} \xrightarrow{d'} & \text{id}_{d_{n-1}^+} e \end{aligned}$$

By construction, we see that $\ell \in E_{n+1}$. By Propositions 1.11, 1.13 and 1.15, we see that $\ell' \in \text{bieq}_{n+1} \mathcal{D}$, and in particular $\ell' = \ell' \begin{array}{cc} * & \text{id}_{d_n^- \ell'} \end{array} \in E_{n+1}$, so we get that $E$ is a bi-invertibility set containing $e$, as desired. $\square$

**Proposition 1.17** ([Ric20, Lemma 14]). *Let $\mathcal{D}$ be an $\omega$-category and $n > 0$. Given $a \in \text{bieq}_n \mathcal{D}$, if $a^L$ and $a^R$ are, respectively, a left and right weak inverse for $a$, then $a^L, a^R \in \text{bieq}_n \mathcal{D}$.*

*Proof.* A bi-invertibility set in the sense of Definition 1.6 containing $a^L$ is constructed in Lemma 1.16, and one for $a^R$ can be constructed with a similar argument. It follows from Definition 1.7 that $a^L, a^R \in \text{bieq}_n \mathcal{D}$, as desired. $\square$

**Lemma 1.18.** *Given an $\omega$-category $\mathcal{D}$, we have that $\text{bieq} \mathcal{D} := \coprod_{n>0} \text{bieq}_n \mathcal{D}$ is an invertibility set.*

*Proof.* Given $a \in \text{bieq}_n \mathcal{D}$, by Definition 1.6 there exist $a^L, a^R \in \mathcal{D}_n$ and $c, c' \in \text{bieq}_{n+1} \mathcal{D}$ of the form

$$c: & a^L \begin{array}{cc} * & a \\ n-1 & \end{array} \to \text{id}_{d_{n-1}^-} a \quad \text{and} \quad c': & a \begin{array}{cc} * & a \\ n-1 & \end{array} \xrightarrow{x} & a^R \to \text{id}_{d_{n-1}^+} a.$$

If $c'^L \in \mathcal{D}_{n+1}$ is a left inverse for $c'$, we set $\ell \in \mathcal{D}_{n+1}$ to be the composite

$$\ell: & a \begin{array}{cc} * & a^L \\ n-1 & \end{array} \xrightarrow{\text{id}_a \begin{array}{cc} * & a^L \\ n-1 & \end{array} \begin{array}{cc} * & c \\ n-1 & \end{array}} & a \begin{array}{cc} * & a^L \\ n-1 & \end{array} \xrightarrow{x} & a^R \xrightarrow{\text{id}_a \begin{array}{cc} * & c \\ n-1 & n-1 \end{array} \begin{array}{cc} * & \text{id}_a R \end{array}} & a \begin{array}{cc} * & c' \\ n-1 & \end{array} \xrightarrow{d} & a^R \xrightarrow{c'} & \text{id}_{d_{n-1}^+} a.$$

By Proposition 1.17 we know that $a^L \in \text{bieq}_n \mathcal{D}$, and by Propositions 1.11, 1.13, 1.15 and 1.17 we know that $\ell \in \text{bieq}_{n+1} \mathcal{D}$. Given that we also have that $c \in \text{bieq}_{n+1} \mathcal{D}$, this shows that $\text{bieq} \mathcal{D}$ is an invertibility set, as desired. $\square$

**Proposition 1.19** ([Ric20, Corollary 19]). *Let $\mathcal{D}$ be an $\omega$-category and $n > 0$. Given $a \in \mathcal{D}_n$, we have that $a \in \text{eq}_n \mathcal{D}$ if and only if $a \in \text{bieq}_n \mathcal{D}$.*

*Proof.* If $a \in \text{eq}_n \mathcal{D}$ (resp. $a \in \text{bieq}_n \mathcal{D}$), a bi-invertibility set (resp. invertibility set) containing $a$ is constructed in Remarks 1.5 and 1.8 (resp. Lemma 1.18). It follows from Definition 1.7 (resp. Definition 1.3) that $a \in \text{bieq}_n \mathcal{D}$ (resp. $a \in \text{eq}_n \mathcal{D}$), as desired. $\square$