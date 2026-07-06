20

Eliminating reversals from cubical type theories

data, the types of pairs  \( (\overline{\mathbf{a}}_{10},\overline{\mathbf{a}}_{\bullet0}) \)  and  \( (\overline{\mathbf{a}}_{1\bullet},\overline{\mathbf{a}}_{\bullet\bullet}) \)  as in (1) are dependent F-singletons, so contractible by Corollary 56. The type of pairs  \( (\overline{\mathbf{a}}_{01},\overline{\mathbf{a}}_{0\bullet}) \)  is likewise a dependent G-singleton and thus contractible. After contracting all of these, we are left with  \( p^{\prime}:GPath(A^{\prime},a_{0}^{\prime},a_{1}^{\prime}) \)  and  \( \overline{a}_{0\bullet}:GPath(\langle x\rangle\overline{A}(0,x,a_{0},p^{\prime}\otimes_{G}x),\overline{a}_{00},\widehat{a}_{01}) \)  where  \( \widehat{a}_{01} \)  is some expression. The type of such pairs is equivalent to  \( GPath(\langle x\rangle\Sigma a^{\prime}:A^{\prime}(x),\overline{A}(0,x,a_{0},a^{\prime}),(a_{0}^{\prime},\widehat{a}_{00}),(a_{1}^{\prime},\widehat{a}_{01})) \) , which is a GPath-type over a contractible type and thus contractible. A symmetric argument deals with the case where we fix  \( p^{\prime} \)  and allow p to vary freely.

▶ Component 58 (S, universes). Using the assumption that  \( FU = GU = U \) , we interpret the universe U by the relation sending A : U and  \( A' : U \)  to the type of U-valued 1-to-1 correspondences between A and  \( A' \) . That this relation is itself a 1-to-1 correspondence is a consequence of univalence of U [39, Theorem 5.8.4(iv)⇒(v)]. We interpret EI, again using the assumption  \( FEI(A) = GEI(A) = EI(A) \) , as extracting the 1-to-1 correspondence.

▶ Component 59 (S, glue). To define SGlue, we are given inputs

\((\mathsf{A},\mathsf{A}^{\prime},\overline{\mathsf{A}})\) : MTy e : \([\mathsf{P}]\to \mathsf{T}\simeq_{F}\mathsf{A}\)   
\((\mathsf{P},\mathsf{P}^{\prime},\overline{\mathsf{P}})\) : MCof e' : \([\mathsf{P}^{\prime}]\to \mathsf{T}^{\prime}\simeq_{G}\mathsf{A}^{\prime}\)   
T : \([\mathsf{P}]\to \mathsf{Ty}\) \(\overline{\mathsf{e}}\) : \([\overline{\mathsf{P}} ]\to \mathsf{R}_{\simeq}(\overline{\mathsf{A}},\overline{\mathsf{T}},\mathsf{e},\mathsf{e}^{\prime})\)   
\(\mathsf{T}^{\prime}\) : \([\mathsf{P}^{\prime}]\to \mathsf{Ty}\)   
\(\overline{\mathsf{T}}\) : \(([\overline{\mathsf{P}} ],\mathsf{t}:\mathsf{T},\mathsf{t}^{\prime}:\mathsf{T}^{\prime})\to \mathsf{Ty}\)

where  \( \overline{A} \)  and  \( \overline{T} \)  are 1-to-1 correspondences and  \( R_{\simeq}(\overline{A},\overline{T},-,-) \)  is the 1-to-1 correspondence between  \( T\simeq_{F}A \)  and  \( T'\simeq_{G}A' \)  given by the span interpretation of  \( (-\simeq-) \)  at  \( \overline{T} \)  and  \( \overline{A} \) . We need to define a 1-to-1 correspondence between  \( FGlue(A,P,T,e) \)  and  \( GGlue(A',P',T',e') \) . We take the relation sending g:  \( FGlue(A,P,T,e) \)  and  \( g':GGlue(A',P',T',e') \)  to

\[
\operatorname{Glue} \left(\overline {{\mathrm{A}}} \left(F \text {unglue} (\mathrm{g}), G \text {unglue} \left(\mathrm{g} ^ {\prime}\right)\right), \overline {{\mathrm{P}}}, \overline {{\mathrm{T}}} \left(\mathrm{g}, \mathrm{g} ^ {\prime}\right), \overline {{\mathrm{e}}}\right)
\]

where it remains to define \(\widehat{\mathbf{e}}:\overline{\mathrm{T}} (\mathbf{g},\mathbf{g}^{\prime})\simeq \overline{\mathrm{A}} (F\mathrm{unglue}(\mathbf{g}),G\mathrm{unglue}(\mathbf{g}^{\prime}))\) under \(\overline{\mathrm{P}}\)

By the reduction equations for \( F \) unglue(g) and \( G \) unglue(g') under P and P', the type for \( \widehat{\mathbf{e}} \) simplifies to \( \overline{\mathrm{T}}(\mathbf{g},\mathbf{g}') \simeq \overline{\mathrm{A}}(\mathbf{e}.1(\mathbf{g}),\mathbf{e}'.1(\mathbf{g}')) \). Per the interpretations of \( \Sigma \) and \( \Pi \) (Components 47 and 54), \( \widehat{\mathbf{e}} \) contains a map \( (\mathbf{t}:\mathbf{T},\mathbf{t}':\mathbf{T}') \to \overline{\mathrm{T}}(\mathbf{t},\mathbf{t}') \to \overline{\mathrm{A}}(\mathbf{e}.1(\mathbf{t}),\mathbf{e}'.1(\mathbf{t}')) \) as its first component. We take this map, instantiated at g and g', as the forward function of \( \widehat{\mathbf{e}} \). To see that it is an equivalence, it suffices [29, Theorem 11.1.6] to check that the induced map on total spaces \( (\Sigma \mathbf{t}:\mathbf{T}.\overline{\mathrm{T}}(\mathbf{t},\mathbf{g}')) \to (\Sigma \mathbf{a}:\mathbf{A}.\overline{\mathrm{A}}(\mathbf{a},\mathbf{e}'.1(\mathbf{g}'))) \) is an equivalence, as the base map e.l: T → A is an F-equivalence and thus an equivalence. This is the case because \( \overline{\mathrm{A}} \) and \( \overline{\mathrm{T}} \) are 1-to-1 correspondences and thus both sides are contractible.

With this interpretation of Glue, we can give the interpretations of glue and unglue as glue and unglue.

To interpret suspension, we make essential use of identity types.

▶ Definition 60. Over the environment ([A : Ty, A' : Ty], f : A → A'), define the type-valued relation Graph(f) := ⟨a, a'⟩(f(a) ≍ a') : (a : A, a' : A') → Ty.

For a map \( \mathbf{f} \) that is an equivalence, \( \text{Graph}(\mathbf{f}) \) is a 1-to-1 correspondence. Conversely, a 1-to-1 correspondence \( \overline{\mathbf{A}} \) between \( \mathbf{A} \) and \( \mathbf{A}' \) contains a map \( \text{fwd}_{\overline{\mathbf{A}}} : \mathbf{A} \to \mathbf{A}' \) that is an equivalence.

Over the environment ([A : Ty, A' : Ty], f : A → A'), define map(f) : FSusp(A) → GSusp(A') by FSusp-elimination so that map(f)(Fnorth) = Gnorth, map(f)(Fsouth) = Gsouth, and cong_map(f)(Fmerid(a)) ∼ Gmerid(a'). If f : A → A' is an equivalence, then map(f) is an equivalence, by the elimination principles for FSusp(A) and GSusp(A').