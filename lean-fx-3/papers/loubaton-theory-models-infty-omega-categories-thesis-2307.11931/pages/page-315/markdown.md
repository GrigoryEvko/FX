6.1. UNIVALENCE

By definition, $\mathrm{LFib}(\langle a,C\rangle)$ is the fully faithful sub $(\infty,1)$-category of the left hand $(\infty,1)$-category corresponding to objects that are local with respect to the image of set of morphism $\{\langle g,0\rangle,g\in\mathrm{W}\}_{/\langle a,C\rangle}$ by the localization functor

$$(\mathrm{Psh}^{\infty}(\Theta\times\Delta)_{/\langle a,C\rangle})\to(\mathrm{Psh}^{\infty}(\Theta\times\Delta)_{/\langle a,C\rangle})_{\{\langle b,\{0\}\rangle\to\langle b,[\mathrm{n}]\rangle\}_{/\langle a,C\rangle}}.$$

Such $\infty$-presheaves corresponds via the equivalence (6.1.1.6) to functors $C\to\mathrm{Psh}^{\infty}(\Theta)_{/a}$ that are pointwise $\mathrm{W}_{/a}$-local. As $\mathrm{W}_{/a}$-local $\infty$-presheaves on $\Theta_{/a}$ corresponds to elements of $(\infty,\omega)$-cat$_{/a}$, we have an equivalence

$$\mathrm{LFib}(\langle a,C\rangle)\sim\mathrm{Fun}(C,(\infty,\omega)\text{-cat}_{/a}).$$

6.1.1.7. A morphism $f:A\to B$ between two $\infty$-presheaves on $\Theta\times\Delta$ induces an adjunction

$$f_{!}:(\infty,\omega,1)\text{-cat}/A\xrightleftharpoons{\quad}(\infty,\omega,1)\text{-cat}_{/B}:f^{*}\tag{6.1.1.8}$$

where $f_{!}$ is the composition and $f^{*}$ is the pullback. As $\mathrm{LFib}(A)$ is the localization of $(\infty,\omega,1)\text{-cat}_{/A}$ along the class of morphisms $\widehat{\mathrm{J}_{/A}}$, the previous adjunction induces a derived adjunction:

$$\mathbf{L}f_{!}:\mathrm{LFib}(A)\xrightleftharpoons{\quad}\mathrm{LFib}(B):\mathbf{R}f^{*}\tag{6.1.1.9}$$

where $\mathbf{L}f_{!}$ sends $E$ onto $\mathbf{F}f_{!}E$ and $\mathbf{R}f^{*}$ is just the restriction of $f^{*}$ to $\mathrm{LFib}(B)$.

6.1.1.10. We denote by $\pi_{!}:\mathrm{Fun}(\Delta^{op},\mathrm{Psh}^{\infty}(\Theta))\to\mathrm{Psh}^{\infty}(\Delta[\Theta])$ the functor induced by extension by colimits by the canonical morphism $\pi:\Delta\times\Theta\to\Delta[\Theta]$. We also define $\mathrm{N}_{(\omega,1)}:\mathrm{Psh}^{\infty}(\Delta[\Theta])\to\mathrm{Fun}(\Delta^{op},\mathrm{Psh}^{\infty}(\Theta))$ as the right adjoint of $\pi_{!}$. As $\pi_{!}$ preserves representable, $\mathrm{N}_{(\omega,1)}$ preserves colimits. Remark that the image of $T$ by $\pi_{!}$ is contained in $\widehat{\mathrm{M}}$, and $\mathrm{N}_{(\omega,1)}$ induces then by restriction a functor

$$\mathrm{N}_{(\omega,1)}:(\infty,\omega)\text{-cat}\to(\infty,\omega,1)\text{-cat}.$$

If $C$ is an $(\infty,\omega)$-category, $\mathrm{N}_{(\omega,1)}C$ corresponds to the simplicial object in $(\infty,\omega)$-cat:

$$\dots\qquad\coprod_{x_{0},x_{1},x_{2}:\tau_{0}C}\mathrm{hom}_{C}(x_{0},x_{1},x_{2})\xrightleftharpoons{\quad}\coprod_{x_{0},x_{1}:\tau_{0}C}\mathrm{hom}_{C}(x_{0},x_{1})\xrightleftharpoons{\quad}\coprod_{x_{0}:\tau_{0}C}1$$

If $p:X\to\mathrm{N}_{(\omega,1)}C$ is a left fibration, and $x$ an object of $C$, we will denote by $X(x)$ the fiber of $p_{0}:X_{0}\to\mathrm{N}_{(\omega,1)}C$ on $x$, and $E(x)$ the canonical morphism $X(x)\to 1$. Unfolding the definitions, and using corollary 4.2.1.50, we then have for any integer $n$ a canonical equivalence:

$$X_{n}\sim\coprod_{x_{0},\dots,x_{n}}X(x_{0})\times\mathrm{hom}_{C}(x_{0},\dots,x_{n})$$

305