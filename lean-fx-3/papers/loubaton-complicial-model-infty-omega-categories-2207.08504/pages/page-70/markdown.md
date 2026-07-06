CHAPTER 2. STUDY OF COMPLICIAL SETS

Definition 2.2.1.7 (Verity). Let $n \in \mathbb{N} \cup \{\omega\}$. A $n$-complicial set is a stratified set having the right lifting property against all elementary anodyne extensions and against all morphisms $[k] \to [k]_t$ for $k > n$.

Theorem 2.2.1.8 (Ozornova, Rovelli, Verity). Let $n \in \mathbb{N} \cup \{\omega\}$. There exists a nice model structure on stratified simplicial sets, denoted by $\mathrm{tPsh}(\Delta)^n$, whose fibrant objects are $n$-complicial sets.

A left adjoint $F : \mathrm{tPsh}(\Delta) \to D$ to a model category is a left Quillen functor if it preserves cofibrations and sends all elementary anodyne extensions and morphisms $[k] \to [k]_t$, for $k > n$, to weak equivalences.

Proof. This is [OR20b, theorem 1.25].

Remark 2.2.1.9. The corresponding theorem for non-saturated complicial sets was originally proven by Verity in [Ver08c].

During this chapter, we will only be interested in the model structure for $\omega$-complicial sets, and we will therefore drop the index $\omega$. The $\omega$-complicial sets will then just be called complicial sets and we will denote by $\mathrm{tPsh}(\Delta)$ the model category $\mathrm{tPsh}(\Delta)^\omega$.

Proposition 2.2.1.10. Let $C$ be a nice model structure, and $F : \mathrm{tPsh}(\Delta)^1 \to C$ a left adjoint that preserves monomorphisms. The functor $F$ is a left Quillen functor if and only if it sends the following morphisms to weak equivalences:

(1) the morphisms of the set $\mathrm{W}_1$ defined in 1.1.2.15.
(2) for any integer $n \ge 2$, the morphism $[n] \to [n]_t$.
(3) the morphism $[1]_t \to [0]$.

Proof. Suppose first that $F$ is a left Quillen functor. According to [RV22, proposition E.2.8.], the functor $F(\_)^b : \mathrm{Psh}(\Delta) \to C$ is a left Quillen functor when $\mathrm{Psh}(\Delta)$ is endowed with the Joyal model structure. According to proposition 3.7.4 of [Cis19], it sends spine inclusions to weak equivalences. As $E^{eq} \to [0]$ is a weak equivalence of this model structure, it is also sent to a weak equivalence. Finally, as $[n] \to [n]_t$ for $n \ge 2$, and $[1]_t \to [0]$ are weak equivalences in $\mathrm{tPsh}(\Delta)^1$, they are sent to weak equivalences by $F$.

To show the other direction, suppose given a functor $F$ fulfilling the desired property. We denote by $S$ the class of cofibrations that are sent to weak equivalences by $F$. The class $S$ is then closed under 2 out of 3, by pushouts and contains the spine inclusions $\mathrm{Sp}_{[n]} \to [n]$.

Remark that for all integer $n$, the morphism $\mathrm{Sp}_{[n+1]} \to \mathrm{Sp}_{[n]} \star [0]$ is a sequence of pushouts along $\mathrm{Sp}_{[2]} \to [2]$ and then is in $S$. By two out of three, so is the morphism $\mathrm{Sp}_{[n]} \star [0] \to [n+1]$.

As a consequence, $S$ is closed under the functor $\_ \star [0]$, and so for any integer $n$, by the functor $\_ \star [n]$. As any simplicial set $K$ is the colimit of the Reedy cofibrant diagram $\Delta_{/K} \to \Delta \to \mathrm{Psh}(\Delta)$, and as $\star$ preserves monomorphisms, the theorem 2.1.1.7 implies that $S$ is closed under $\_ \star K$.

Now let $f : X \to Y$ be a morphism in $S$. By stability under pushout of $S$, the morphism

$$X \star [n] \to X \star [n] \coprod_{X \star \partial[n]} Y \star [n]$$

is in $S$. By two out of three, so is the morphism

$$X \star [n] \coprod_{X \star \partial[n]} Y \star \partial[n] \to Y \star [n].$$

70