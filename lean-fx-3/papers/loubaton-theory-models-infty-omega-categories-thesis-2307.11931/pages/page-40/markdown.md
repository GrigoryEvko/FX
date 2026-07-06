CHAPTER 1. THE CATEGORY OF $(0, \omega)$-CATEGORIES

**1.1.2.5.** A *Reedy category* is a small category $A$ equipped with two subcategories $A_+$, $A_-$ and a *degree* function $d : ob(A) \to \mathbb{N}$ such that:

(1) for every non identity morphism $f : a \to b$, if $f$ belongs to $A_-$, $d(a) > d(b)$, and if $f$ belongs to $A_+$, $d(a) < d(b)$.

(2) every morphism of $A$ uniquely factors as a morphism of $A_-$ followed by a morphism of $A_+$.

A Reedy category $A$ is *elegant* if for any presheaf $X$ on $A$, for any $a \in A$ and any $c \in X(a)$, there exists a unique morphism $f : a \to a' \in A_-$ and a unique non degenerate object $c' \in X(a')$ such that $c = X(f)(c')$.

**Proposition 1.1.2.6.** *Let $X$ be a presheaf on an elegant Reedy category $A$. The category $A_{/X}$ is an elegant Reedy category.*

*Proof.* We have a canonical projection $\pi : A_{/X} \to A$. A morphism is positive (resp. negative) if it's image by $\pi$ is. The degree of an element $c$ of $A_{/X}$ is the degree of $\pi(c)$. We leave it to the reader to check that this endows $A_{/X}$ with a structure of Reedy category.

The fact that $A_{/X}$ is elegant is a direct consequence of the isomorphism $\mathrm{Psh}(A_{/X}) \cong \mathrm{Psh}(A)_{/X}$. $\square$

**1.1.2.7.** We define by induction the *dimension* of a globular sum $a$, denoted by $|a|$. The dimension of $[0]$ is $0$, and the dimension of $[\mathbf{a}, n]$ is the maximum of the set $\{|a_k| + 1\}_{k < n}$. We denote by $\Theta_n$ the full subcategory of $\Theta$ whose objects are the globular sum of dimension inferior or equal to $n$.

**Proposition 1.1.2.8** (Berger, Bergner-Rezk). *The category $\Theta$ and, for any $n \in \mathbb{N}$, the category $\Theta_n$ are elegant Reedy category.*

*A morphism $g : [\mathbf{a}, n] \to [\mathbf{b}, m]$ is degenerate (i.e a morphism of $\Theta_-$) if the corresponding morphism $f : [n] \to [m]$ is a degenerate morphism of $\Delta$, and for any $i < n$ and any $f(i) \leq k < f(k+1)$, the corresponding morphism $a_i \to b_k$ is degenerate. Furthermore, a morphism is degenerate if and only if it is a epimorphism in $\mathrm{Psh}(\Theta)$.*

*A morphism is in $\Theta^+$ if and only if it is a monomorphism in $\mathrm{Psh}(\Theta)$.*

*Proof.* The Reedy structure is a consequence of lemma 2.4 of [Ber02]. The fact that for any $n < \omega$, $\Theta_n$ is elegant is [BR13b, corollary 4.5.]. As for any $n < \omega$, the inclusion $\Theta_n \to \Theta$ preserves strong pushout, the characterization of elegant Reedy category given by [BR13b, proposition 3.8.] implies that $\Theta$ is also elegant. $\square$

30