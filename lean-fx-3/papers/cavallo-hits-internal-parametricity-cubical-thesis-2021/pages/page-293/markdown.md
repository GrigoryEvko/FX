# Chapter 16

## Formalism

Building on the parametric formalism and presheaf model developed in Chapter 11, we sketch an extension to a modal parametric type theory. Following the framework developed in Licata and Shulman's *adjoint logic* [LS16] and used in Gratzer et al.'s **MTT** [GKNB20], we express the properties of the context modalities compactly by formulating a *mode theory*.$^{1}$ This consists of the two judgments $m$ mode and $\mu : m \rightarrow n$ we have already encountered as well as a 2-cell judgment $\alpha :: \mu \Rightarrow \nu : m \rightarrow n$ specifying maps between modalities, which together constitute a definition of a strict 2-category [JY20, §2.3]. Each 2-cell $\alpha :: \mu \Rightarrow \nu : m \rightarrow n$ will induce a transformation $\Gamma' \cdot \mu \vdash \gamma \otimes \mu : \Gamma \cdot \mu \otimes m$ between modal contexts. We also annotate each of the previously-existing judgments with a mode.

|  Judgment | Presuppositions | Reading  |
| --- | --- | --- |
|  $m$ mode |  | $m$ is a mode  |
|  $\mu : m \rightarrow n$ | $(m, n \text{ mode})$ | $\mu$ is a modality from $m$ to $n$  |
|  $\alpha :: \mu \Rightarrow \mu' : m \rightarrow n$ | $(\mu, \mu' : m \rightarrow n)$ | $\alpha$ is a 2-cell from $\mu$ to $\mu'$  |
|  $\Gamma$ ctx @ $m$ | $(m \text{ mode})$ | $\Gamma$ is a context at mode $m$  |
|  $\vdots$ | $\vdots$ | $\vdots$  |

The logic of modalities we use—the set of rules mediating $-\mu$ and modal hypotheses—is a mechanical specialization of the **MTT** framework. The negative treatment of the modal type operators Disc and Glo is novel, though it might be viewed as an algebraicization of a Fitch-style calculus [Clo18; BCMEPS20]. The discrete type we use is a restricted version of **MTT**'s formulation of modal types, as discussed in Section 14.4.2.

$^{1}$In those works, the aim is to define a general formalism that can be instantiated at various mode theories, while we are interested only in the specific mode theory describing the cohesive relationship between pointwise and parametric modes. Nevertheless, specification in terms of mode theory judgments is convenient for expressing the functoriality of modalities and naturality of transformations between them concisely.

281