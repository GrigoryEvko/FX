194

Programming with parametricity

Finally, we apply Lemma 10.2.2, reducing this bridge in the isomorphism type to an isomorphism of bridge types; this is where we rely on extent. We are left to show, for every $a : A$ and $b : B$, the following isomorphism.

$$\begin{array}{c} \operatorname{Bridge}(\boldsymbol{x}.\operatorname{Gel}_{\boldsymbol{x}}(A,B,\operatorname{Bridge}(\boldsymbol{x}.p\boldsymbol{x},-,-)),a,b) \\ \simeq \\ \operatorname{Bridge}(\boldsymbol{x}.p\boldsymbol{x},\operatorname{coe}_{-A}^{0\to 1}(a),\operatorname{coe}_{-B}^{0\to 1}(b)) \end{array}$$

We have a pair of paths $\lambda^{\sharp}y.\operatorname{coe}_{-A}^{y\to 1}(a)\in\operatorname{Path}(A,\operatorname{coe}_{-A}^{0\to 1}(a),a)$ and $\lambda^{\sharp}y.\operatorname{coe}_{-B}^{y\to 1}(b)\in\operatorname{Path}(B,\operatorname{coe}_{-A}^{0\to 1}(b),b)$, so we can delete the coercions in the above. This leaves us to show $\operatorname{Bridge}(\boldsymbol{x}.\operatorname{Gel}_{\boldsymbol{x}}(A,B,\operatorname{Bridge}(\boldsymbol{x}.p\boldsymbol{x},-,-)),a,b)$ is isomorphic to $\operatorname{Bridge}(\boldsymbol{x}.p\boldsymbol{x},a,b)$. This is an instance of the inverse condition we have already proven, instantiated at the relation $\operatorname{Bridge}(\boldsymbol{x}.p\boldsymbol{x},-,-)$. $\square$

### 10.3 Bridge-discrete types

In classical parametricity, the *identity extension lemma* is a key basic result: it says that the relational interpretation of an operator on types takes identity relations to identity relations. In particular, the interpretation of any closed type is the identity relation. In internal parametricity, the corresponding statement would be that any "homogeneous" bridge type $\operatorname{Bridge}(A,M_0,M_1)$—where $A$ is a type rather than a line $\boldsymbol{x}:\mathbf{I}\gg A$ type—is isomorphic to $\operatorname{Path}(A,M_0,M_1)$, the relation $\operatorname{Bridge}(A,-,-)$ being the analogue of the relational interpretation of $A$. We have just seen that this is false: we have $\operatorname{Bridge}(\mathrm{U},A,B)\simeq(A\times B\to\mathrm{U})\neq(A\simeq B)\simeq\operatorname{Path}(\mathrm{U},A,B)$. We can, however, identify the types that *do* satisfy this property, which we call the *bridge-discrete types*. We will see that the class of bridge-discrete types is closed under every type former we have introduced *except* the universe, and that assumptions of bridge-discreteness can effectively play the role of the identity extension lemma.

A bit more precisely, we define the bridge-discrete types to be those for which the canonical map from paths to bridges is an isomorphism.

**Definition 10.3.1.** Let $A$ type be given. We define a map $\operatorname{loosen}_A$ as follows, so that $\operatorname{loosen}_A\in\operatorname{Path}(A,a_0,a_1)\to\operatorname{Bridge}(A,a_0,a_1)$ for any $a_0,a_1:A$.

$$\operatorname{loosen}_A:=\lambda p.\operatorname{coe}_{x.\operatorname{Bridge}(A,p\,0,p\,x)}^{0\to 1}(\lambda^{\mathbf{I}}.-p\,0)$$

We say $A$ is *bridge-discrete* if $\operatorname{loosen}_A$ is an isomorphism for every pair of endpoints, *i.e.*, if the following type is inhabited.

$$\operatorname{IsBDisc}(A):=(a_0,a_1:A)\to\operatorname{IsIso}(\operatorname{Path}(A,a_0,a_1),\operatorname{Bridge}(A,a_0,a_1),\operatorname{loosen}_A)$$