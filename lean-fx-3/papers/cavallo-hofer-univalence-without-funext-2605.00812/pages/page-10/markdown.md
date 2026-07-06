CAVALLO, HÖFER

## 4 Familial categorical univalence in the polynomial model

Fix an input model $\mathbb{C}$ as in Section 3. To study $\mathsf{CUA}_{\mathcal{U}}^{\bullet}$ in $\mathbf{Poly}(\mathbb{C})$, we analyze the wild category $\mathcal{U}^{I}$ and its isomorphisms. To simplify calculations, we redefine here $\mathcal{U}^{I}(A,B):=\prod_{u:\sum_{I}A}B(\pi_{0}u)$. This is strictly isomorphic to the type $\prod_{i:I}A(i)\to B(i)$ in Definition 1.4, so the two versions of $A\cong_{\mathcal{U}^{I}}B$ are related by an equivalence preserving the identity isomorphism up to path. Hence, $\mathsf{CUA}_{\mathcal{U}}^{\bullet}$ is invariant under this change.

We start by unfolding the type $\mathcal{U}^{I}(A,B)$ and composition in $\mathcal{U}^{I}$. A key observation is that the shape part of $f\in\mathrm{Tm}(\Gamma,A\to B)$ consists of a function between shapes and a *partial* function between positions.

**Lemma 4.1** *For $\Gamma\in\mathbf{Poly}(\mathbb{C})$, $I\in\mathrm{Ty}(\Gamma)$, and $A,B\in\mathrm{Ty}(\Gamma.I)$, the type $\mathcal{U}^{I}(A,B)\in\mathrm{Ty}(\Gamma)$ is given by*

$$\Gamma_{S}\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\vdash\mathcal{U}^{I}(A,B)_{S}\stackrel{*}{=}\sum_{f_{S}:\mathcal{U}^{I_{S}}(A_{S},B_{S})}\prod_{\substack{i:I_{S}\\ a:A_{S}(i)}}B_{P}(i,f_{S}(i,a))\to 1+\big(I_{P}(i)+A_{P}(i,a)\big),$$

$$\Gamma_{S},\langle f_{S},f_{P}\rangle\colon\mathcal{U}^{I}(A,B)_{S}\vdash\mathcal{U}^{I}(A,B)_{P}\stackrel{*}{=}\sum_{\substack{i:I_{S},a:A_{S}(i)\\ b:B_{P}(i,a,f_{S}(a))}}\mathfrak{is}_{0}(f_{P}(i,a,b))$$

**Proof.** Direct unfolding using Propositions 3.7 and 3.12.

**Lemma 4.2** *If $f\in\mathrm{Tm}(\Gamma,\mathcal{U}^{I}(B,C))$, $g\in\mathrm{Tm}(\Gamma,\mathcal{U}^{I}(A,B))$, then the composite $fg\in\mathrm{Tm}(\Gamma,\mathcal{U}^{I}(A,C))$ is given by*

$$\Gamma_{S}\vdash(fg)_{SS}\stackrel{*}{=}f_{SS}\circ g_{SS}\colon\mathcal{U}^{I_{S}}(A_{S},C_{S}),$$

$$\Gamma_{S}\vdash(fg)_{SP}\stackrel{*}{=}\lambda i.\lambda a.[\mathfrak{in}_{0},\mathfrak{in}_{0},g_{SP}(i,a)]\circ f_{SP}(g_{SS}(i,a))\colon\prod_{\substack{i:I_{S}\\ a:A_{S}(i)}}C_{P}(i,(fg)_{SS}(a))\to 1+\big(I_{P}(i)+A_{P}(i,a)\big).$$

**Proof.** We have that $\mathrm{Tm}(\Gamma,\mathcal{U}^{I}(A,B))\cong\mathrm{Tm}(\Gamma.I.A,B\mathfrak{p})$. Let $u\in\mathrm{Tm}(\Gamma.I.B,C\mathfrak{p})$ and $v\in\mathrm{Tm}(\Gamma.I.A,B\mathfrak{p})$ given by $u_{S}\in\mathrm{Tm}(\Gamma_{S}.I_{S}.B_{S},C_{S}\mathfrak{p})$, $v_{S}\in\mathrm{Tm}(\Gamma_{S}.I_{S}.A_{S},B_{S}\mathfrak{p})$, $u_{P}\colon C_{P}\langle\mathfrak{p},u_{S}\rangle\to(\Gamma_{P}+I_{P})\mathfrak{p}+B_{P}$ in $\mathbf{Ty}(\Gamma_{S}.I_{S}.B_{S})$, and $v_{P}\colon B_{P}\langle\mathfrak{p},v_{S}\rangle\to(\Gamma_{P}+I_{P})\mathfrak{p}+A_{P}$ in $\mathbf{Ty}(\Gamma_{S}.I_{S}.A_{S})$. The composite of $u$ and $v$ is by definition $u\langle\mathfrak{p},v\rangle\in\mathrm{Tm}(\Gamma.I.A,C\mathfrak{p})$. Direct calculation using Definition 3.5 and Proposition 3.6 shows that $(u\langle\mathfrak{p},v\rangle)_{S}=u_{S}\langle\mathfrak{p},v_{S}\rangle$ and $(u\langle\mathfrak{p},v\rangle)_{P}=[\mathfrak{in}_{0},v_{P}]\circ u_{P}\langle\mathfrak{p},v_{S}\rangle\colon C_{P}u_{S}\langle\mathfrak{p},v_{S}\rangle\to(\Gamma_{P}+I_{P})\mathfrak{p}+A_{P}$. Composing with the $\lambda$-app bijection from Proposition 3.12 yields the desired description.

### 4.1 Categories of partial functions

We now introduce an auxiliary wild category in $\mathbb{C}$. It can be viewed as the Kleisli category of the monad on $\mathcal{U}^{I}$ given by coproduct with a fixed family $J\colon I\to\mathcal{U}$, though we will not explicitly develop this viewpoint. To see that this even is a wild category in our setting, we rely on the strict properties of coproducts.

**Proposition 4.3 (In $\mathbb{C}$)** *For every family $J\colon I\to\mathcal{U}$, the following defines a wild category $\mathcal{U}_{J}^{I}$:*

$$(\mathcal{U}_{J}^{I})_{0}:=\mathcal{U}^{I},\quad(\mathcal{U}_{J}^{I})_{1}(A,B):=\prod_{i:I}A(i)\to J(i)+B(i),\quad(\mathrm{id}_{A})_{i}:=\mathfrak{in}_{1},\quad(f\circ g)_{i}:=[\mathfrak{in}_{0},f_{i}]\circ g_{i},$$

*with unitors and associators given by reflexivity.*

**Proof.** Direct calculation using the $\eta$ rules for $\Pi$ and $+$.

Morphisms in $\mathcal{U}_{J}^{I}$ can be thought of as families of partial functions, with $J$ as a type of “errors”. We introduce a notion of *total* morphism in $\mathcal{U}_{J}^{I}$. By $\eta$ for coproducts, total morphisms coincide with morphisms in $\mathcal{U}^{I}$ up to equivalence. Crucially, all isomorphisms in $\mathcal{U}_{J}^{I}$ will be total.

**Definition 4.4 (In $\mathbb{C}$)** A morphism $f\colon\mathcal{U}_{J}^{I}(A,B)$ is *total* if $\mathfrak{is}\text{-tot}(f):=\prod_{i:I,a:A(i)}\mathfrak{is}_{1}(f_{i}a)$ is inhabited. We define $\mathcal{U}_{J,\mathrm{tot}}^{I}(A,B):=\sum_{f:\mathcal{U}_{J}^{I}(A,B)}\mathfrak{is}\text{-tot}(f)$.

10