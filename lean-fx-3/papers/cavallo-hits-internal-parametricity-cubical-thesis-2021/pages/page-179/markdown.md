# Chapter 9

## Parametric cubical type theory

We now enrich the cubical type theory defined in Part I with a *bridge interval*—an interval for internal parametricity—and its attendant type formers and operators, as developed by Bernardy, Coquand, and Moulin [BCM15]. At each stage, we will be revisiting a cubical element from a new angle. Unsurprisingly, the bridge interval parallels the path interval, as do bridge types path types. In addition, the function extensionality principle is paralleled by a new extent operator, while V types are paralleled by Gel types.

Of course, none of these parallels are exact. The differences between cubical and parametric type theory have two sources. The first is mundane: we do not expect to be able to coerce along relations as we can along equivalences, so the bridge interval comes with no notion of coercion or composition. Happily, this means the parametric extension is rather less technically involved than the cubical. The second is more interesting: the bridge interval does not support *contraction*. This means we are prohibited from performing substitutions, like the one shown below, which substitute the same bridge variable for two different variables.

$$z : \mathbf{I} \Vdash (z/x, z/y) \in (x : \mathbf{I}, y : \mathbf{I}) \quad \times$$

In the traditional parlance of substructural logic, bridge interval hypotheses are *affine*. The differences between the cubical constructs and their cubical equivalents nearly all flow from this single modification to the interval theory.

The original cubical model of identity types, the BCH model of Bezem, Coquand, and Huber [BCH13], also used an affine interval. Bernardy, Coquand, and Moulin's internal parametricity therefore naturally adopted the same structure [BCM15]. Cubical type theory later drifted to a structural approach; affinity is more problematic for higher inductive types, and is simply unnecessarily complex when a structural interval will do. We will see here that it is, on the other hand, indispensable for internal parametricity.

167