8:12

Antoine Van Muylder, Andreas Nuyts, and Dominique Devriese

The $\beta$-rule of extent is not a standard type theoretic rule, as it works by capturing (see CAP rule) the bridge variable argument $x : \text{BI}$ of extent in its principal argument $a : Ax$. Capturing can only be performed if a specific freshness constraint (semi-freshness, denoted sfresh$(a, x)$) is satisfied and thus EXT-$\beta$ only fires in that case. We now explain what semi-freshness is and how capturing is implemented. Note that several other parametricity primitives of Agda --bridges like Gel and the Kan operations make use of capturing in their equations.

Definition 2.2 (Semi-freshness constraint). Given a context $\Gamma = \Gamma_1, (x : \text{BI}), \Gamma_2$ and a term $\Gamma \vdash a$, the constraint sfresh$(a, x)$ is satisfied if for every free variable $v$ of $a$ one of the following holds:

- $v \in \Gamma_1$ or $v = x$,
- $(v : \text{I}) \in \Gamma_2$ or$^3$ $(v : \text{BI}) \in \Gamma_2$. We define $\Upsilon_2$ as the variables $v$ satisfying this clause.

If $\Gamma_1, (x : \text{BI}), \Gamma_2 \vdash a : Ax$ and sfresh$(a, x)$ then $a$ is in fact a weakening $a = a'[\pi]$ of a term $\Gamma_1, (x : \text{BI}), \Upsilon_2 \vdash a' : A'x$ along $\pi : \Gamma_1, (x : \text{BI}), \Gamma_2 \to \Gamma_1, (x : \text{BI}), \Upsilon_2^4$. Moreover, there is a well-typed substitution $\rho : \Gamma_1, (x : \text{BI}), \Gamma_2, (y : \text{BI}) \to \Gamma_1, (x : \text{BI}), \Upsilon_2$ defined by $\rho = (\text{id}_{\Gamma_1}, y/x, \text{id}_{\Upsilon_2})$, so that we have $\Gamma_1, (x : \text{BI}), \Gamma_2, (y : \text{BI}) \vdash a'[\rho] : A'[\rho]y$. Agda --bridges will shortcut this by constructing a potentially ill-typed substitution $\sigma = (\text{id}_{\Gamma_1}, y/x, \text{id}_{\Upsilon_2}) : \Gamma_1, (x : \text{BI}), \Gamma_2, (y : \text{BI}) \to \Gamma_1, (x : \text{BI}), \Gamma_2$ which has the property that $\pi \circ \sigma = \rho$, and therefore $\Gamma_1, (x : \text{BI}), \Gamma_2, (y : \text{BI}) \vdash a[\sigma] = a'[\rho] : A[\sigma]y$ is well-typed. By freshness w.r.t. $x, A[\sigma] = A$ and by lambda abstraction we obtain $\Gamma \vdash \lambda y. a[\sigma] : (@y : \text{BI}) \to Ay$. The latter is the definition of capturing $\Gamma \vdash \langle x \rangle a : (@y : \text{BI}) \to Ay$.

## 2.5 Gel Types

The univalence theorem stated in Section 2.1.3 posits that paths at the universe $AA : A_0 \equiv A_1$ uniquely correspond to type equivalences $A_0 \simeq A_1$. Analogously, the relativity theorem asserts that bridges at the universe uniquely correspond to relations.

$$\text{relativity} : (A_0 \to A_1 \to \text{Type}) \simeq \text{Bridge}_{\text{Type}} A_0 A_1$$

Similar to extent, Agda --bridges postulates the existence of Gel in order to validate the left-to-right direction of relativity. Thus Gel has the following type (see also GEL-FORM in Fig. 1).

$$\text{Gel} : \forall (A_0 A_1 : \text{Type}) (R : A_0 \to A_1 \to \text{Type}) (@\text{tick } x : \text{BI}) \to \text{Type}$$

The type of Gel merely ends with a type of affine functions (@$x : \text{BI}$) $\to$ Type which can be turned into a bridge type thanks to the GEL-$\partial$ rule.

To upgrade this map into the relativity equivalence, we first need an inverse candidate. From a bridge between two types $AA : \text{Bridge}_{\text{Type}} A_0 A_1$ we obtain the following relation $\lambda a_0 a_1 \to \text{Bridge}_{\text{x}, AAx} a_0 a_1 : A_0 \to A_1 \to \text{Type}$. This relation between the types $A_0$ and $A_1$ holds for $a_0, a_1$ exactly when there is a dependent bridge over $AA$ between them. We also need to provide two inverse conditions.

2.5.1 The First Inverse Condition. Regarding the first condition, using function extensionality one has to show $\forall (R : A_0 \to A_1 \to \text{Type})(a_0 : A_0)(a_1 : A_1) \to \text{Bridge}_{\text{x}, \text{Gel}A_0 A_1 Rx} a_0 a_1 \equiv R a_0 a_1$. By univalence, it can be reduced to proving an equivalence $\text{Bridge}_{\text{x}, \text{Gel}A_0 A_1 Rx} a_0 a_1 \simeq R a_0 a_1$. One could call this equivalence a (dependent) relational extensionality principle for Gel. Constructing both directions of this particular equivalence is precisely the role played by the introduction and elimination primitives of Gel, called gel and ungel, respectively (see GEL-INTRO, GEL-ELIM). The fact that gel and ungel are mutual inverses is in turn guaranteed by the equations governing those primitives, called the $\eta$-rule and the $\beta$-rule of Gel (see GEL-$\beta$, GEL-$\eta$). Note that the $\eta$-rule of Gel

$^4$Because $Ax$ is a well-typed bridge application, $A$ is fresh w.r.t. $x$ and therefore $A = A'[\pi]$.

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.