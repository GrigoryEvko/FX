Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:9

The addition of modal annotations creates a redundancy in our system: we may hypothesize of $\langle\mu\mid A\rangle$ with annotation $\nu$ or directly hypothesize over $A$ with annotation $\nu\circ\mu$. There is a substitution navigating in one direction, but not the other:

$$\Gamma.(\nu\circ\mu\mid A)\vdash\uparrow.\mathsf{mod}_{\mu}(\mathbf{v}_{0}):\Gamma.(\nu\mid\langle\mu\mid A\rangle)\circledast o$$

This mismatch is addressed through elimination for $\langle\mu\mid-\rangle$. Informally, this rule ensures that these two contexts are isomorphic 'from the perspective of a type':$^{5}$

$$\begin{array}{c} \nu:m\longrightarrow o\qquad\mu:n\longrightarrow m\\ \Gamma\mathsf{cx}\circledast o\qquad\Gamma.\{\nu\}.\{\mu\}\vdash A\circledast n\qquad\Gamma.(\nu\mid\langle\mu\mid A\rangle)\vdash B\circledast m\\ \frac{\Gamma.\{\nu\}\vdash M_{0}:\langle\mu\mid A\rangle\circledast m\qquad\Gamma.(\nu\circ\mu\mid A)\vdash M_{1}:B[\uparrow.\mathsf{mod}_{\mu}(\mathbf{v}_{0})]\circledast o}{\Gamma\vdash\mathsf{let}_{\mu}\mathsf{mod}_{\nu}(\_)\leftarrow M_{0}\text{ in }M_{1}:B[\mathsf{id}.M_{0}]\circledast o} \end{array}$$

$$\mathsf{let}_{\mu}\mathsf{mod}_{\nu}(\_)\leftarrow\mathsf{mod}_{\nu}(M_{0})\text{ in }M_{1}=M_{1}[\mathsf{id}.M_{0}]$$

Notice that the elimination rule for the modal type $\langle\mu\mid-\rangle$ is parameterized by an additional modality $\nu$. We refer to $\mu$ as the main modality and $\nu$ as the framing modality.

**Remark 2.2.** Fitch-style type theories require $\Gamma.(\nu\circ\mu\mid A)\vdash\uparrow.\mathsf{mod}_{\mu}(\mathbf{v}_{0}):\Gamma.(\nu\mid\langle\mu\mid A\rangle)\circledast o$ to be invertible. Such an inverse, however, again disrupts substitution in the presence of multiple modalities. For an extended discussion of this point and various potential solutions, see Gratzer et al. [GCK$^{+}$22].

In addition to modal types, dependent products in MTT are also modalized so that $A\to B$ is replaced by $(\mu\mid A)\to B$:

$$\frac{\Gamma.(\mu\mid A)\vdash M:B\circledast m}{\Gamma\vdash\lambda(M):(\mu\mid A)\to B\circledast m}\qquad\frac{\Gamma\vdash M:(\mu\mid A)\to B\circledast m\qquad\Gamma.\{\mu\}\vdash N:A\circledast n}{\Gamma\vdash M(N):B[\mathsf{id}.N]\circledast m}$$

This feature is a useful convenience; it ensures that many functions avoid the need to accept an argument of modal type only to immediately apply the elimination rule. We will see frequent examples of this pattern later as MTT is used as a metalanguage.

**2.3. Standard combinators within MTT.** As the assignment $\Gamma\mapsto\Gamma.\{\mu\}$ is pseudo-functorial, its adjoint action on types is likewise functorial up to propositional equality. In particular, there are equivalences $\mathsf{triv}:\langle\mathsf{id}\mid A\rangle\to A$ and $\mathsf{comp}:\langle\mu\mid\langle\nu\mid A\rangle\rangle\to\langle\mu\circ\nu\mid A\rangle$:

$$\begin{array}{l} \mathsf{triv}(x)=\mathsf{let}_{\mathsf{id}}\mathsf{mod}_{\mathsf{id}}(y)\leftarrow x\text{ in }y\\ \mathsf{triv}^{-1}(x)=\mathsf{mod}_{\mathsf{id}}(x)\\ \mathsf{comp}(x)=\mathsf{let}_{\mathsf{id}}\mathsf{mod}_{\mu}(y_{0})\leftarrow x\text{ in }\mathsf{let}_{\mu}\mathsf{mod}_{\nu}(y_{1})\leftarrow y_{0}\text{ in }\mathsf{mod}_{\mu\circ\nu}(y_{1})\\ \mathsf{comp}^{-1}(x)=\mathsf{let}_{\mathsf{id}}\mathsf{mod}_{\mu\circ\nu}(y)\leftarrow x\text{ in }\mathsf{mod}_{\mu}(\mathsf{mod}_{\nu}(y)) \end{array}$$

Each modality $\langle\mu\mid-\rangle$ also satisfies the modal principle referred to as axiom $K$ i.e., they preserve finite products. In practice, this property serves as an internalization of functoriality as it provides a canonical comparison map $\langle\mu\mid A\to B\rangle\to\langle\mu\mid A\rangle\to\langle\mu\mid B\rangle$. In fact, we can prove a dependent version of this map as in Birkedal et al. [BCM$^{+}$20]:

$$(\ast):\langle\mu\mid(x:A)\to B(x)\rangle\to(a:\langle\mu\mid A\rangle)\to\mathsf{let}\mathsf{mod}_{\mu}(a_{0})\leftarrow a\text{ in }\langle\mu\mid B(a_{0})\rangle$$

$^{5}$Formally, this rule ensures that, among others, this map is anodyne in the sense of Awodey [Awo18].