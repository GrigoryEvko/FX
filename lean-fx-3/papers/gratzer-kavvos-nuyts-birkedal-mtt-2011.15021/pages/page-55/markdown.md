Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:55

10.3. Recovering the adjunction internally. The foregoing construction of a model interpreted the lock functors required by $\mathcal{M}_{\mathrm{adj}}$ by an adjunction. Consequently, substitutions $\Delta \to \Gamma, \widehat{\bullet}_{\mu}$ are in natural bijection with substitutions $\Delta, \widehat{\bullet}_{\nu} \to \Gamma$. We would like to strengthen this setting by bootstrapping this adjunction into an internal adjunction.

It is not immediately clear what an internal adjunction should be. However, we can construct an appropriate definition by internalizing the unit and counit as functions. But that is not immediate either: if $\Gamma \vdash A \text{ type}_1 @ m$, the construction $\langle \mu \mid \langle \nu \mid A \rangle \rangle$ that we would naively try as the codomain of the unit is ill-typed. This can be mended through key substitutions. Recall that $\eta : 1_m \Rightarrow \mu \circ \nu$. The corresponding key substitution at $\Gamma @ m$ is $\widehat{\bullet}_{\Gamma}^{\eta} : \Gamma, \widehat{\bullet}_{\mu \circ \nu} \to \Gamma @ m$. We can use this to formally define the notation of Section 2.3 by

$$A^{\eta} \triangleq A[\widehat{\bullet}_{\Gamma}^{\eta}]$$

As substitutions can be eliminated (e.g. through a subset of the canonicity algorithm), this defines an admissible operation from type $\Gamma \vdash A \text{ type}_1 @ m$ to type $\Gamma, \widehat{\bullet}_{\mu \circ \nu} \vdash A^{\eta} \text{ type}_1 @ m$. We can thus define the unit component at $\Gamma \vdash A \text{ type}_1 @ m$ by

$$\text{unit} \quad : A \to \langle \mu \mid \langle \nu \mid A^{\eta} \rangle \rangle @ m$$

$$\text{unit}(x) \triangleq \text{mod}_{\mu}(\text{mod}_{\nu}(x^{\eta}))$$

Dually, for any type $\Gamma, \widehat{\bullet}_{\nu \circ \mu} \vdash A \text{ type}_1 @ n$ we can define the counit component by

$$\text{counit} \quad : \langle \nu \mid \langle \mu \mid A \rangle \rangle \to A^{\epsilon} @ n$$

$$\text{counit}(x) \triangleq \text{let mod}_{\nu}(y_0) \leftarrow x \text{ in let}_{\nu} \text{mod}_{\mu}(y_1) \leftarrow y_0 \text{ in } y_1^{\epsilon}$$

We thus obtain the unit and counit internally, but the types of the components have to be adjusted in the presence of dependence. Moreover, we can prove internal versions of the triangle equations; they are given by modal induction:

$$_{-} : (x : \langle \nu \mid A \rangle) \to \text{Id}_{\langle \nu | A \rangle}(x, \text{counit}(\text{mod}_{\nu}(\text{unit}) \circledast_{\nu} x))$$

$$_{-} \triangleq \lambda x. \text{ let mod}_{\nu}(y) \leftarrow x \text{ in refl}(\text{mod}_{\nu}(y))$$

$$_{-} : (x : \langle \mu \mid A \rangle) \to \text{Id}_{\langle \mu | A \rangle}(x, \text{mod}_{\mu}(\text{counit}) \circledast_{\mu} \text{unit}(x))$$

$$_{-} \triangleq \lambda x. \text{ let mod}_{\mu}(y) \leftarrow x \text{ in refl}(\text{mod}_{\mu}(y))$$

The most difficult part is proving that these terms are well-typed. For example, in the first instance we must show that $\text{mod}_{\nu}(y) = \text{counit}(\text{mod}_{\nu}(\text{unit}) \circledast_{\nu} \text{mod}_{\nu}(y))$ definitionally:

$$\text{counit}(\text{mod}_{\nu}(\text{unit}) \circledast_{\nu} \text{mod}_{\nu}(y)) = \text{counit}(\text{mod}_{\nu}(\text{unit}(y)))$$

$$= \text{counit}(\text{mod}_{\nu}(\text{mod}_{\mu}(\text{mod}_{\nu}(y^{\eta}))))$$

$$= \text{mod}_{\nu}(y^{\eta})^{\epsilon}$$

$$= \text{mod}_{\nu}((y^{\eta})^{\epsilon \star 1_{\nu}})$$

$$= \text{mod}_{\nu}(y^{(\epsilon \star 1_{\nu}) \circ (1_{\nu} \star \eta)})$$

$$= \text{mod}_{\nu}(y)$$

Because we are using slightly informal syntax here, it is difficult to see that the steps that introduce whiskering are correct. They become much more perspicuous if we expand $\text{mod}_{\nu}(y^{\eta})^{\epsilon}$ into algebraic syntax, and use the last equation of Fig. 9 twice to absorb locks:

$$\text{mod}_{\nu}(y[\widehat{\bullet}_{\Gamma, \widehat{\bullet}_{\nu}}^{\eta}])[\widehat{\bullet}_{\Gamma}^{\epsilon}] = \text{mod}_{\nu}(y[\widehat{\bullet}_{\Gamma, \widehat{\bullet}_{\nu}}^{\eta} \circ \widehat{\bullet}_{\Gamma, \widehat{\bullet}_{\nu}}^{\epsilon}]) = \text{mod}_{\nu}(y[\widehat{\bullet}_{\Gamma}^{1_{\nu} \star \eta} \circ \widehat{\bullet}_{\Gamma}^{\epsilon \star 1_{\nu}}]) = \text{mod}_{\nu}(y[\widehat{\bullet}_{\Gamma}^{1_{\mu}}])$$