# Chapter 11

## Formalism and models

To extend the cubical formalism sketched in Section 3.3 to include parametricity primitives, the essential task is to develop an algebraic equivalent of the interval restriction operator $-\setminus r$, which is necessary to capture the affine quality of bridge interval variables. In the type theory of Chapter 9, $-\setminus r$ is defined as an operator on raw contexts; like substitution as an operator on raw terms, this must be avoided in an algebraic formalism.

In the following, we therefore develop a novel formulation that regards $-\setminus r$ as a primitive context former, characterized by an adjoint relationship with context extension by an interval variable. We note that this issue is not addressed in Bernardy, Coquand, and Moulin's account of internal parametricity [BCM15]. In the formalism they present, rules that we would express using restriction are expressed by including interval variables in the context of the conclusion as in the following rule for bridge elimination.

$$\frac{\Gamma \cdot I \vdash A \text{ type} \quad \Gamma \vdash M_0 : A[0_I] \quad \Gamma \vdash M_1 : A[1_I] \quad \Gamma \vdash P : \text{Bridge}(A, M_0, M_1)}{\Gamma \cdot I \vdash P v_I : A}$$

While this does ensure bridge variables are only used affinely, the calculus fails to satisfy cut elimination, which in the algebraic setting means that it is not always possible to reduce away an explicit substitution. In this case, there is no way to reduce $(Pv_I)[\gamma]$ given $\Gamma' \vdash \gamma : \Gamma \cdot I$. In our calculus, by contrast, this term can reduce to $P[\gamma \setminus v_I]v_I[\gamma]$, using the functorial action of interval restriction on substitutions.

In addition to the judgments of Section 3.3, we now have judgments for well-formedness and equality of bridge interval variables.

|  Judgment | Presuppositions | Reading  |
| --- | --- | --- |
|  $\Gamma \vdash r : I$ | ($\Gamma$ ctx) | $r$ is a bridge interval variable  |
|  $\Gamma \vdash r = r' : I$ | ($\Gamma \vdash r, r' : I$) | $r$ and $r'$ are equal bridge interval variables  |

209