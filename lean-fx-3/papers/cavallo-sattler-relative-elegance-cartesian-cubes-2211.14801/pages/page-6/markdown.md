6

E. Cavallo and C. Sattler

obstructions are avoided in the cubical models by working with uniform fibrations, which classically coincide with ordinary fibrations but provide necessary extra structure in the constructive case. However, there are obstructions to constructing a universe classifying uniform fibrations in simplicial sets [BF22, Appendix D; Swa22, §8.4.1].

Henry [Hen25] discovered that the Kan–Quillen model structure can be constructivized by instead modifying the class of cofibrations, in particular taking a simplicial set to be cofibrant only when degeneracy of its cells is decidable. Alternative constructions of the same model structure were later presented by Gambino, Sattler, and Szumiło [GSS22]. Gambino and Henry [GH22] exhibit a constructive form of Voevodsky's simplicial model of HoTT using these ideas. The problem is not entirely settled, however: the left adjoint splitting coherence construction [LW15], applied to the classical simplicial model to obtain a strict model of type theory, does not apply constructively in this case [GH22, Remark 8.5]. There has since been progress on coherence theorems that do apply here [Boc22; GL21], but the question is not to our knowledge fully resolved. Separately, van den Berg and Faber [BF22] have identified and developed a theory of effective fibrations of simplicial sets, which are both closed under pushforward and support a classifying universe, but have not yet addressed the interpretation of univalence.

### 1.1.5 Constructivity

Though our interest in cubical-type model structures is motivated by constructive concerns, we work entirely and incautiously within a classical metatheory in this article, our goal being an equivalence with a classically defined model structure. Given that $\widehat{\square}_{\nu}^{iy}$ is constructively definable, however, it is natural to wonder whether it is constructively equivalent with the ACCRS or constructive simplicial model structures. We leave this question for the future, referring to Shulman [Shu23] for further discussion of the constructive homotopy theory of spaces.

We note that the triangulation functor T: PSh($\square_{\nu}$) $\to$ PSh($\Delta$) (Definition 4.35) is definitely not a left Quillen adjoint from $\widehat{\square}_{\nu}^{iy}$ to Henry's simplicial model structure constructively, as it does not preserve cofibrations unless the excluded middle holds. The (triangulation, nerve) adjunction exhibits PSh($\Delta$) as a reflective subcategory of PSh($\square_{\nu}$), so every simplicial set is the triangulation of some cubical set. But while every cubical set is cofibrant in $\widehat{\square}_{\nu}^{iy}$, not every simplicial set is cofibrant in Henry's model structure. For example, given a subsingleton set P, the pushout of the span $\Delta^1 \leftarrow \Delta^1 \times P \rightarrow P$ is cofibrant if and only if P is decidable.

### 1.1.6 Reedy, non-Reedy, and Reedy-like categories

Campion [Cam23] studies the existence and non-existence of elegant Reedy structures on various cube categories, among them $\square_{\nu}$ (under the name $\square_{d,c^{\vee},s}$). A few observations are made independently in that article and our own; in particular, [Cam23, Proposition 8.3] is our Theorem 4.46, while [Cam23, Theorem 8.12(2)] follows from our Proposition A.1.

Shulman's almost c-Reedy categories [Shu15, Definition 8.8] generalize beyond generalized Reedy categories. These allow for non-isomorphisms that do not factor through a lower-degree object, so one may wonder if the aforementioned pathological map $u: [1]^3 \to [1]^3$ in $\square_{\nu}$ (and $\overline{\square}_{\nu}$) defined by $(x, y, z) \mapsto (x \vee y, y \vee z, z \vee x)$ can be

2025/10/16 00:43