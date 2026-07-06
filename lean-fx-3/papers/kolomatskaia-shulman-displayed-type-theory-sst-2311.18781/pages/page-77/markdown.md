presheaves, in which the 'contexts' over $\Gamma$ are morphisms of telescopes $\theta_{01}: \Theta_1 \to \Theta_0$ over $\Gamma$, and the 'types' in such a 'context' over $\Gamma$ are pairs of two telescopes $\Upsilon_0 \in \text{Tel}(\Gamma \mid \Theta_0)$ and $\Upsilon_1 \in \text{Tel}(\Gamma \mid \Theta_1 \mid \Upsilon_0[\theta_{01}])$. This is no longer strongly democratic, but as always we have the strict CwF morphism $(-)_0: \text{Tel}^2 \to \text{Tel}$ that preserves $\Sigma$-types (i.e. telescope concatenation), and the pseudo CwF-morphism $(-)_1: \text{Tel}^2 \to \text{Tel}$. Moreover, in this case the latter is actually a strict CwF-morphism, because telescope concatenation is strictly associative.

**Definition 4.35.** Let $\mathcal{C}: \mathcal{M}^{\text{coop}} \to \mathcal{Cat}$ be a dTT natural model with telescopes. We say $\mathcal{C}$ has telescope display if it is equipped with

1. An internal pseudo CwF morphism that preserves substitution, the empty context, and $\Sigma$-types strictly:

$$(-)^d: (\widehat{\bullet}_{\Delta\square})^*\text{Tel}_{sm} \to \text{Tel}_{sm}^2$$

2. An equality between the composite $(\widehat{\bullet}_{\Delta\square})^*\text{Tel}_{sm} \xrightarrow{(-)^d} \text{Tel}_{sm}^2 \xrightarrow{(-)_0} \text{Tel}_{sm}$ and the key transformation $(-)[\mathcal{Q}_{\widehat{\bullet}}^{\Delta\square\in\mathbb{1}_{sm}}]: (\widehat{\bullet}_{\Delta\square})^*\text{Tel}_{sm} \to \text{Tel}_{sm}$. Since the latter is a strict morphism, that means that so is the former.

3. A strict internal CwF morphism

$$(-)^D: (\widehat{\bullet}_{\Delta\square})^*\text{Tel}_{sm} \to \text{Tel}_{sm}$$

and an isomorphism of pseudo CwF morphisms between $(-)^D$ and the composite morphism $(\widehat{\bullet}_{\Delta\square})^*\text{Tel}_{sm} \xrightarrow{(-)^d} \text{Tel}_{sm}^2 \xrightarrow{(-)_1} \text{Tel}$, that is the identity on underlying functors.

We have not assumed *a priori* in definition 4.35 that $\mathcal{C}$ has décalage, but it is actually included: the morphism $(-)^D$ is of course the same as in definition 4.34, and the transformation $\text{evens}: \Theta^D \to \Theta$ from definition 4.34 arises in definition 4.35 as the image of $\Theta$ under the underlying functor of $(-)^d$. The additional data in definition 4.35 beyond this is the 1-part of the action of $(-)^d$ (the 0-part is determined by the composition with $(-)_0$ equaling $(-)[\mathcal{Q}_{\widehat{\bullet}}^{\Delta\square\in\mathbb{1}_{sm}}]$) making it a pseudo CwF morphism preserving substitution and $\Sigma$-types strictly, and the isomorphism on 'types' (dependent telescopes) between $(-)^D$ and the composite of $(-)^d$ with $(-)_1$. But since the latter is to be a pseudo CwF transformation (see [CCD17, Appendix B]), and since $(-)^D$ is strict and the underlying functor is the identity this just means that this isomorphism must coincide with the 1-part of the comprehension coherence isomorphism of $(-)^d$ (the 0-part being the identity).

So all that remains is the 1-part of the action of $(-)^d$ on meta-abstracted telescopes, preserving substitution and telescope concatenation, and coherence isomorphisms relating it to comprehension. This gives the rules of section 2.6.4, which have section 2.6.3 as a special case. In particular, since the 1-part of the comprehension of $(\Upsilon, \Upsilon^d)$ in $\text{Tel}^2$ is $(\Upsilon \mid \Upsilon^d)$, the comprehension isomorphisms are the pairing $\langle -, - \rangle$ together with $^{\text{ev}}$ and $^{\text{od}}$.

Finally, we consider display of types, as in section 2.4.3, and its relation to décalage as in sections 2.4.4 and 2.6.2. In some ways this is simpler, since we don't have to worry about rearranging between display and décalage; but in other ways it is more complicated, since we have to take account of extending dependent telescopes by types.

To start with, note that the internal telescope model $\text{Tel}$ of any CwF has a 'sub-model' $\text{Tel}_1$ whose internal category of 'contexts' is the same (telescopes), but whose internal presheaf of 'types' consists of the *length-1 telescopes*, i.e. single types annotated by a modality. Note that unlike $\text{Tel}$, it does not automatically have $\Sigma$-types.

77