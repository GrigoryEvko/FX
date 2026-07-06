16:48

A. NUYTS AND D. DEVRIESE

Vol. 20:2

|  name | FreshMLTT | MTraS  |
| --- | --- | --- |
|  name quantification | \( \mathsf{N}[i:N].T \) | \( \langle \mathsf{N}(i:\mathbb{I})\mid [T]\rangle \)  |
|  name abstraction | \( \alpha[i:N].t \) | \( \mathsf{mod}_{\mathsf{N}(i:\mathbb{I})}[[t]] \)  |
|  name application | \( t@i \) | \( \mathsf{app}_{i}\cdot_{\mathbb{I}[i]}[[t]] \)  |
|  non-binding quant. | \( \langle \langle i:N\rangle\rangle.T \) | \( \langle \mathbb{I}[i]\mid \langle \mathsf{N}i\mid [T][\mathsf{R}_{\mathsf{copy}_i}^{\mathsf{app}_i}]\rangle \rangle \)  |
|  non-binding abs. | \( \langle i:N\rangle.t \) | \( \mathsf{copy}_i[[t]]:= \mathsf{mod}_{\mathbb{I}[i]}(\mathsf{mod}_{\mathsf{N}i}([t][\mathsf{R}_{\mathsf{copy}_i}^{\mathsf{app}_i}])) \)  |
|  locally fresh name | \( \nu[i:N].t \) | \( \mathsf{drop}_{i}\cdot_{\mathsf{N}i}(\mathsf{mod}_{\mathbb{I}[i]}[[t]]) \)  |

Figure 12: A heuristic for translating FreshMLTT [PMD15] to the current system.

simplifies to  \( \langle\forall u\mid T\rangle \) . When  \( \varphi \)  holds and t = weld a = ga, then the weld-constructor of the right hand Weld-type reduces to  \( (\text{mod}_{\forall u}g)\circledast\sqcup \)  which effectively applies g under the  \( mod_{\forall u} \) -constructor, so that both clauses match as required.

10.6. Locally fresh names. Nominal type theory is modelled in the Schanuel topos [Pit14] which is a subcategory of nullary affine cubical sets  \( \mathrm{Psh}(^{0}\mathrm{Cube}_{\square}) \)  (Example 6.14). As fibrancy is not considered in this paper, we will work directly in  \( \mathrm{Psh}(^{0}\mathrm{Cube}_{\square}) \) . Names can be modelled using the multiplier  \( \sqcup*(i:\mathbb{I}) \) . Interestingly, the fresh weakening functor  \( \mathbb{I}_{(i:\mathbb{I})} \)  is then inverse to its left adjoint  \( \exists_{(i:\mathbb{I})} \) . By consequence, we get  \( \exists i\cong\forall i=:N i \)  (the fresh name quantifier) with inverse  \( \mathbb{I}[i]\cong\mathbb{I}[i] \) . For consistency, we will only use N i and  \( \mathbb{I}[i] \) , and these will be each other's left names. The relevant 2-cells are  \( app_{i}:\mathbb{I}[i]\circ N i\Rightarrow1 \)  and its inverse  \( copy_{i}:1\Rightarrow\mathbb{I}[i]\circ N i \)  (these are each other's left names), as well as  \( const_{i}:1\Rightarrow N i\circ\mathbb{I}[i] \)  and its inverse  \( drop_{i}:N i\circ\mathbb{I}[i]\Rightarrow1 \)  (these are each other's left names).

The nominal dependent type system FreshMLTT [PMD15] used in Pitts's examples of interest [Pit14] is substantially different from ours:

- It features a name swapping operation that is semantically not merely a substitution.
- Freshness for a name \( i \) is not a modality or a type, but a judgement that can be derived for an expression \( t \) if and only if \( t \) is invariant under swapping \( i \) with a newly introduced name \( j \). As a consequence, freshness propagates through type and term constructors.
- Many equalities are strict where we can only guarantee an isomorphism.

For these reasons, we do not try to formally state that we can support locally fresh names in the sense of FreshMLTT. Nevertheless, in Fig. 12 we give at least a heuristic \(\llbracket \sqcup \rrbracket\) for translating programs in a subsystem of FreshMLTT to programs in the current system. This subsystem does not feature name swapping, but it does feature the non-binding abstractions originally defined in terms of it, as well as locally fresh names.

Ordinary name quantification is simply translated to the modality \(\mathcal{N}i\), and as usual application corresponds to the modal projection function (Proposition 3.3). The non-binding abstraction in FreshMLTT abstracts over a name that is already in scope, without shadowing, i.e. it is a variable capturing operation. This is translated essentially to the 2-cell \(\mathrm{copy}_i:1\Rightarrow \mathbb{I}[i]\circ \mathcal{N}i\), which is inverse to \(\mathrm{app}_i\) as we have seen earlier for a variable capturing operation (Section 10.2). Finally, a locally fresh name abstraction \(\nu [i:N].t\) brings a name \(i\) into scope in its body \(t\), but requires that \(t\) be fresh for \(i\); in our system we would say that \(t\) is a subterm of modality \(\mathcal{N}i\circ \mathbb{I}[i]\). The type of \(\nu [i:N].t\) is the same as the type of \(t\), which we can justify with the isomorphism \(\mathrm{drop}_i:\mathcal{N}i\circ \mathbb{I}[i]\cong 1\). This isomorphism is essentially the content of the modal projection function of \(\mathbb{I}[i]\), which we use to translate locally fresh name abstractions.