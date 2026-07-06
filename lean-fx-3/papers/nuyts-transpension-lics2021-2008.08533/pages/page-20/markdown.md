16:20

A. NUYTS AND D. DEVRIESE

Vol. 20:2

to frame the shape context $\mathbb{X}$ as the *mode* of the judgement, as it determines the category $\mathrm{Psh}(\mathcal{W}/\Xi)$ in which the judgement is modelled.

Concretely, we fix a set of **shapes** and generate shape contexts by the following rules:

|   | SHP-CTX-EXT  |
| --- | --- |
|  SHP-CTX-EMPTY | $\mathbb{X}$ shpctx $\mathbb{U}$ shape  |
|  · shpctx | $\mathbb{X}, u : \mathbb{U}$ shpctx  |

In Section 8.2, we will additionally add boundary variables. More generally, users of the current system could add shape context constructors at will, as long as they can be interpreted as presheaves over $\mathcal{W}$.

**4.2. Mode theory.** For simplicity, we take a highly general mode theory and will then only be able to say interesting things about specific modalities and 2-cells. In practice, and especially in implementations, one will want to select a more syntactic subtheory right away.

As **modes**, we take shape contexts. An interpretation function $[\sqcup]$ from shape contexts to presheaves over $\mathcal{W}$ will be defined in Section 6.1. The mode $\mathbb{X}$ is modelled in $\mathrm{Psh}(\mathcal{W}/[\mathbb{X}])$.$^9$

As **modalities** $\mu : \mathbb{X}_1 \to \mathbb{X}_2$, we take all functors $[\mathbf{\Omega}_\mu] : \mathrm{Psh}(\mathcal{W}/[\mathbb{X}_2]) \to \mathrm{Psh}(\mathcal{W}/[\mathbb{X}_1])$ which have a right adjoint $[\mu]$ that is then automatically a weak CwF morphism [Nuy20b] [Nuy20a, thm. 6.4.1] giving rise to a DRA [BCM$^+$20, lemma 17][Nuy18a, §2.1.3].$^{10}$

As **2-cells** $\alpha : \mu \Rightarrow \nu$, we take all natural transformations $[\mathbf{\Omega}_\alpha] : [\mathbf{\Omega}_\nu] \to [\mathbf{\Omega}_\mu]$, which automatically give rise to natural transformations $[\alpha] : [\mu] \to [\nu]$.

## 5. MTRAS MODALITIES FOR SUBSTITUTION

In the previous section, we have defined modalities as left adjoint functors and 2-cells as natural transformations. As such, we have neglected to provide an actual syntax; any syntax we use should be shallowly defined on semantic objects.

We take a similar approach to shape substitutions. A shape substitution from $\mathbb{X}_1$ to $\mathbb{X}_2$ is defined as a presheaf morphism $\sigma : [\mathbb{X}_1] \to [\mathbb{X}_2]$. We will consistently write the interpretation brackets so as to avoid confusion with modalities $\mathbb{X}_1 \to \mathbb{X}_2$. A presheaf morphism *is* not a modality but it gives rise to a pair of modalities:$^{11}$

**Theorem 5.1.** *Any presheaf morphism $\sigma : \Xi_1 \to \Xi_2$ gives rise to a triple of adjoint functors*

$$\Sigma^{\sigma|} \dashv \Omega^{\sigma|} \dashv \Pi^{\sigma|},$$

$$\Sigma^{\sigma|}, \Pi^{\sigma|} : \mathrm{Psh}(\mathcal{W}/\Xi_1) \to \mathrm{Psh}(\mathcal{W}/\Xi_2) \qquad \Omega^{\sigma|} : \mathrm{Psh}(\mathcal{W}/\Xi_2) \to \mathrm{Psh}(\mathcal{W}/\Xi_1)$$

$^9$As we will see later on, the available shapes must in some sense already be present in the base category, so that a context consisting purely of shapes will in general be representable. As such, we could alternatively interpret modes as *representable* presheaves over $\mathcal{W}$, which via the Yoneda-embedding are just the objects of $\mathcal{W}$. This is perfectly possible and would (again by inserting the Yoneda-embedding) require virtually no changes to our approach, although a number of intermediate results in the technical report [Nuy20b] would become unnecessary. However, the current approach is strictly more general, allows us to speak about boundaries (definitions 6.6 and 6.23) in the shape context, and did not require any compromise in the strength of our results.

$^{10}$A designated right adjoint can be retrieved from the left adjoint without the axiom of choice [Nuy20b, §2.3.6].

$^{11}$Note in particular that $\Omega[\sqcup]$ turns the arrow around: a presheaf morphism (shape substitution) $\sigma : [\mathbb{X}_1] \to [\mathbb{X}_2]$ gives rise to a substitution modality $\Omega[\sigma] : \mathbb{X}_2 \to \mathbb{X}_1$ sending types $T$ in shape context $\mathbb{X}_2$ to types $\langle \Omega[\sigma] \mid T \rangle$ in shape context $\mathbb{X}_1$.