# The main statement

Among measurable sets of a fixed area on a sphere, two opposite spherical caps have the smallest orthogonality shadow. Every minimizer whose area is strictly between zero and the whole sphere agrees almost everywhere with such a pair of caps.

## Precise shadow theorem

Let $n \ge 3$, and let $\sigma$ be uniform surface measure on the unit sphere $S^{n-1} \subset \mathbb{R}^n$, normalized so that the whole sphere has measure $1$.

For any set $A$ measurable in the completion of this measure, its **orthogonality shadow** is

$$
\mathrm{Sh}(A)
= \lbrace y \in S^{n-1} : \text{there exists } x \in A \text{ with } x \cdot y = 0 \rbrace.
$$

In words, the shadow consists of every direction perpendicular to at least one point of $A$.

Write $p = \sigma(A)$, and choose the unique $r \in [0,\pi/2]$ such that

$$
p = \frac{\int_0^r \sin^{n-2}(t)\,dt}
         {\int_0^{\pi/2} \sin^{n-2}(t)\,dt}.
$$

Then

$$
\sigma_*(\mathrm{Sh}(A))
\ge \frac{\int_0^r \cos^{n-2}(t)\,dt}
          {\int_0^{\pi/2} \sin^{n-2}(t)\,dt}.
$$

Here $\sigma_*(B)$ is the supremum of the measures of compact subsets of $B$. This makes the statement meaningful even when the actual shadow is not measurable. The input set $A$ need not be antipodally symmetric.

The bound is attained by the two opposite open caps

$$
C(a,r) = \lbrace x \in S^{n-1} : |a \cdot x| > \cos r \rbrace,
\qquad a \in S^{n-1}.
$$

If $0 < p < 1$, equality forces $A$ to agree with some $C(a,r)$ outside a set of measure zero. This is an implication from equality; it does not assert that arbitrary changes on null sets preserve the literal shadow.

On real projective space $\mathbb{RP}^{n-1}$, opposite points of the sphere are identified. The two caps become a single projective ball, which minimizes the projective orthogonality shadow at fixed normalized volume, with the same bound and rigidity.

## The double-cap consequence

Every measurable subset of $S^{n-1}$ containing no two orthogonal vectors has measure at most

$$
\delta_n = \frac{\int_0^{\pi/4} \sin^{n-2}(t)\,dt}
                {\int_0^{\pi/2} \sin^{n-2}(t)\,dt}.
$$

Two opposite **open** caps of angular radius $45^\circ$ attain this maximum. Every maximizing set agrees almost everywhere with such a pair.

This follows because a set containing no orthogonal pair is disjoint from its own shadow, so its measure plus the inner measure of its shadow is at most $1$.

On the ordinary sphere $S^2$, the maximum is

$$
1 - \frac{1}{\sqrt{2}} \approx 0.292893.
$$

## Source declarations

This is a natural-language reconstruction of the final theorem statements in the source.

- [SharpShadow.lean](LeanShadow/SharpShadow.lean): `arbitrary_shadow_inequality`, `arbitrary_shadow_equality`, and `cap_attains`.
- [ProjectiveShadow.lean](LeanShadow/ProjectiveShadow.lean): `sharp_shadow_inequality`, `sharp_shadow_equality`, and `caps_attain`.
- [DoubleCap.lean](LeanShadow/DoubleCap.lean): `double_cap_bound`, `double_cap_equality`, and `double_cap_attainment`.
- [CapExtremizers.lean](LeanShadow/CapExtremizers.lean): `double_cap_conjecture`, `alpha_eq_delta`, and `s2_double_cap_bound`.
