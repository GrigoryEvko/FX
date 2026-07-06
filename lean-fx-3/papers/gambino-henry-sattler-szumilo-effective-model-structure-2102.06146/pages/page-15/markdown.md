Let us inspect the action of $F$ on the colimit cocone of $p$. It will suffice to show that it results in objectwise colimit cocones. Since the maps of the colimit cocone of $p$ are pullback squares, we obtain pastings of pullback squares upon applying $F$. Recall that $\mathrm{ev}_B$ is computed by evaluation at the object representing $B$. So by assumption, $(\mathrm{colim}\,Y)(B) = \mathrm{ev}_B(\mathrm{colim}\,Y)$ is colimit of $\mathrm{ev}_B \circ Y$ and van Kampen. The claim follows by universality of this van Kampen colimit. $\square$

### 3 An enriched small object argument

The goal of this section is to develop a version of the small object argument that allows us to construct weak factorisation systems on the category of simplicial objects $\mathfrak{s}\mathcal{E}$, where $\mathcal{E}$ is a countably lextensive category. In view of our application to both simplicial objects in Section 4 and semisimplicial objects in Section 12, we develop our small object argument for diagram categories $\mathcal{E}^D$ in general. Importantly, our weak factorisation systems are *enriched*, in the sense of [Rie14]. We will be constructing $\mathrm{Psh}\,\mathcal{E}$-enriched weak factorisation systems on $\mathcal{E}^D$, where $\mathrm{Psh}\,\mathcal{E}$ denotes the category of presheaves over $\mathcal{E}$. This is because the category of diagrams $\mathcal{E}^D$ is not necessarily $\mathcal{E}$-enriched, but it is $\mathrm{Psh}\,\mathcal{E}$-enriched, as we now recall.

For $E \in \mathcal{E}$ and $X \in \mathcal{E}^D$, we define $E \times X \in \mathcal{E}^D$ by letting

$$(E \times X)_d =_{\mathrm{def}} E \times X_d. \quad (3.1)$$

Given $X, Y \in \mathcal{E}^D$, we then define the hom-object $\mathrm{Hom}_{\mathrm{Psh}\,\mathcal{E}}(X, Y) \in \mathrm{Psh}\,\mathcal{E}$ by letting:

$$\begin{array}{rcl} \mathrm{Hom}_{\mathrm{Psh}\,\mathcal{E}}(X, Y) & : & \mathcal{E}^{\mathrm{op}} \to \mathrm{Set} \\ & : & E \mapsto \mathrm{Hom}_{\mathrm{Set}}(E \times X, Y) \end{array}$$

This makes $\mathcal{E}^D$ into a $\mathrm{Psh}\,\mathcal{E}$-enriched category, so that the formula in (3.1) provides the tensor of $E \in \mathrm{Psh}\,\mathcal{E}$ and $X \in \mathcal{E}^D$ with respect to this enrichment. When the presheaf is representable, the representing object is denoted by $\mathrm{Hom}_{\mathcal{E}}(X, Y)$.

Using the enrichment, we can define an internal version of the familiar lifting problems involved in the definition of a weak factorisation systems. For morphisms $i: A \to B$ and $p: X \to Y$ in $\mathcal{E}^D$, we define the *presheaf of lifting problems* of $i$ against $p$ by letting

$$\mathrm{Prob}_{\mathrm{Psh}\,\mathcal{E}}(i, p) =_{\mathrm{def}} \mathrm{Hom}_{\mathrm{Psh}\,\mathcal{E}}(A, X) \times_{\mathrm{Hom}_{\mathrm{Psh}\,\mathcal{E}}(A, Y)} \mathrm{Hom}_{\mathrm{Psh}\,\mathcal{E}}(B, Y).$$

When the relevant hom-objects are representable, then so is $\mathrm{Prob}_{\mathrm{Psh}\,\mathcal{E}}(i, p)$. In this case, we write $\mathrm{Prob}_{\mathcal{E}}(i, p)$ for its representing object and call it the *object of lifting problems* of $i$ against $p$. Note that the induced pullback hom of $i$ and $p$ (cf. Remark 1.2) has the form

$$\widehat{\mathrm{Hom}}_{\mathrm{Psh}\,\mathcal{E}}(i, p) : \mathrm{Hom}_{\mathrm{Psh}\,\mathcal{E}}(B, X) \to \mathrm{Prob}_{\mathrm{Psh}\,\mathcal{E}}(i, p) \quad (3.2)$$

Again, if the objects are representable, we have also an induced pullback hom in $\mathcal{E}$, which has the form

$$\widehat{\mathrm{Hom}}_{\mathcal{E}}(i, p) : \mathrm{Hom}_{\mathcal{E}}(B, X) \to \mathrm{Prob}_{\mathcal{E}}(i, p). \quad (3.3)$$

We are ready to define the $\mathrm{Psh}\,\mathcal{E}$-enriched counterparts of the standard lifting properties.

**Definition 3.1.** Let $i: A \to B$ and $p: X \to Y$ be morphisms of $\mathcal{E}^D$.

- We say that $i$ has the $\mathrm{Psh}\,\mathcal{E}$-enriched *left lifting property* with respect to $p$ and that $p$ has the $\mathrm{Psh}\,\mathcal{E}$-enriched *right lifting property* with respect to $i$ if the induced pullback hom in (3.2) is a split epimorphism in $\mathrm{Psh}\,\mathcal{E}$.

15