118

General higher inductive types

# Functions

$$\frac{a : A \gg \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{N}} = \mathrm{N}' \in \mathrm{B}}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright \lambda a ._{\mathrm{N}} = \lambda a ._{\mathrm{N}}' \in \mathrm{B}} \quad \frac{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{F}} = \mathrm{F}' \in (a : A) \to \mathrm{B} \quad M = M' \in A}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{F}} M = \mathrm{F}' M' \in \mathrm{B}[M/a]}$$

$$\frac{a : A \gg \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{N}} \in \mathrm{B} \quad M \in A}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright (\lambda a ._{\mathrm{N}}) M = \mathrm{N}[M/a] \in \mathrm{B}[M/a]}$$

$$\frac{A \text{ type} \quad a : A \gg \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{B}} \text{ atype} \quad \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{F}} \in (a : A) \to \mathrm{B}}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{F}} = \lambda a ._{\mathrm{F}} a \in (a : A) \to \mathrm{B}}$$

# Paths

$$\frac{x : \mathbb{I} \gg \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{M}} = \mathrm{M}' \in \mathrm{A}}{x : \mathbb{I} \gg \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright \lambda^{\mathbb{I}} x ._{\mathrm{M}} = \lambda^{\mathbb{I}} x ._{\mathrm{M}}' \in \operatorname{PATH}(x ._{\mathrm{A}}, \mathrm{M}[0/x], \mathrm{M}'[1/x])}$$

$$\frac{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{P}} = \mathrm{P}' \in \operatorname{PATH}(x ._{\mathrm{A}}, \mathrm{M}_0, \mathrm{M}_1) \quad r = r' \in \mathbb{I}}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{P}} r = \mathrm{P}' r' \in \mathrm{A}[r/x]}$$

$$\frac{x : \mathbb{I} \gg \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{N}} = \mathrm{N}' \in \mathrm{A} \quad r \in \mathbb{I}}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright (\lambda^{\mathbb{I}} x . N) r = N[r/x] \in A[r/x]}$$

$$\frac{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{P}} = \mathrm{P}' \in \operatorname{PATH}(\mathrm{A}, \mathrm{M}_0, \mathrm{M}_1)}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{P}} = \lambda^{\mathbb{I}} x ._{\mathrm{P}} x \in \operatorname{PATH}(x ._{\mathrm{A}}, \mathrm{M}_0, \mathrm{M}_1)} \quad \frac{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{P}} \in \operatorname{PATH}(x ._{\mathrm{A}}, \mathrm{M}_0, \mathrm{M}_1)}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{P}} \varepsilon = \mathrm{M}_{\varepsilon} \in \mathrm{A}[\varepsilon/x]}$$

# Structural

$$\frac{(a : \mathrm{A}) \in \Theta}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright a \in \mathrm{A}}$$

$$\frac{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{M}} \in \mathrm{A} \quad \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{A}} = \mathrm{B} \text{ atype}}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{M}} \in \mathrm{B}}$$

$$\frac{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{M}} = \mathrm{N} \in \mathrm{A}}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{N}} = \mathrm{M} \in \mathrm{A}}$$

$$\frac{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{M}} = \mathrm{N} \in \mathrm{A} \quad \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{N}} = \mathrm{P} \in \mathrm{A}}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright_{\mathrm{M}} = \mathrm{P} \in \mathrm{A}}$$

Figure 6.4: Inductive definition of argument terms (functions, paths, and structural rules). The ambient context $\Gamma$ is omitted for readability.