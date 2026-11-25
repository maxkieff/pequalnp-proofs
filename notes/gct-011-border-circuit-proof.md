# A border-circuit proof of L-gct-011

November 25, 2026

For every integer $c\ge1$ and every sufficiently large $m$, the complex padded permanent of order $m$ lies outside the determinant orbit closure of order $m^c+1$. In fact, there are absolute constants $b>0$ and $M$ such that, whenever $m\ge M$ and $n\ge m$, membership in that closure requires

$$
n+1\ \ge\ \exp\!\left(b\,\frac{(\log m)^2}{(\log\log m)^2}\right).
$$

The circuit lower bound is due to the authors of *Circuit lower bounds for Hamiltonian cycle and the permanent*. They explicitly deduce the corresponding bound for affine determinants. The argument below applies their theorem to the exact padding, index convention, and topology used by pequalnp. All logarithms are natural. [Project statement](https://data.pequalnp.com/data/lemma/L-gct-011.e0ee1c5dec3d.json) · [November 24 preprint, Theorem 1.1 and its determinant consequence](https://github.com/openai/math/blob/92b516ef8e2abf66c3db7aa31438d3010bc7956f/preprints/Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026/build/intro.tex)

## Proof

Write $N=n+1$, let $z$ denote the $(0,0)$ variable, and write $X$ for the disjoint $m\times m$ block with both indices shifted by one. The project polynomial is $z^{N-m}\operatorname{per}_m(X)$. Assume it belongs to the orbit closure of $\det_N$. By the project definition, a sequence of invertible linear substitutions of $\det_N$ converges coefficientwise to it. In each term set $z=1$, keep $X$, and set all other variables to zero. The resulting polynomials $q_j=\det A_j(X)$ have affine-linear entries and converge coefficientwise to $\operatorname{per}_m(X)$. Indeed, before substitution there are finitely many degree-$N$ monomials in $N^2$ variables, and every coefficient after substitution is a fixed linear combination of those coefficients. This also explains why individual matrix entries can diverge without affecting the argument. [Project definitions](../lean/PEqualNP/Defs/Gct.lean) · [Lean dehomogenization theorem](data/gct-frontier/OrbitSeparation.lean)

For $v=m^2$, each $q_j$ has a binary arithmetic circuit with at most $S=9\max(v,N)^4$ gates when $\max(v,N)\ge1$. Here is one construction over $\mathbb C$. For a pencil $A$ put $d_k=[t^k]\det(I+tA)$ and $B_k=[t^k]\operatorname{adj}(I+tA)$. Start with $d_0=1$, $B_0=I$. Jacobi's formula and the adjugate identity give

$$
U_k=B_kA,\qquad d_{k+1}=\frac{\operatorname{tr}(U_k)}{k+1},\qquad
B_{k+1}=d_{k+1}I-U_k.
$$

After $N$ rounds $d_N=\det A$. The reciprocal of $k+1$ is a complex scalar input. Build the $N^2$ affine entries once for at most $N^2(2v+1)$ gates. In each round, computing all entries of $U_k$ costs at most $2N^3$ gates, and the trace, scalar multiplication and matrix subtraction cost at most $2N+1+N^2$. The total is bounded by $S$, uniformly over the values of the pencil parameters. The Lean calculation below implements this recurrence. The preprint obtains a polynomial bound over arbitrary fields from Berkowitz's algorithm. [Checked circuit construction](data/gct-frontier/DetPencilCircuit.lean) · [Berkowitz's determinant algorithm](https://doi.org/10.1016/0020-0190(84)90018-8) · [Determinant consequence in the preprint](https://github.com/openai/math/blob/92b516ef8e2abf66c3db7aa31438d3010bc7956f/preprints/Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026/build/intro.tex#L95-L110)

Let $\pi_m$ retain just the degree-$m$ coefficients in the $m^2$ variables. Then $\pi_m q_j$ converges to the coefficient vector of the homogeneous polynomial $\operatorname{per}_m$. Every polynomial equation vanishing on the degree-$m$ outputs of size-$S$ circuits vanishes on each $\pi_m q_j$. It vanishes at their limit by continuity. This proves precisely the Zariski-closure membership in Theorem 1.1. Over $\mathbb C$, that theorem gives an absolute $a>0$ such that at **every** sufficiently large order,

$$
  \exp(a h(m))\le 9\max(m^2,N)^4,
  \qquad h(m)=\frac{(\log m)^2}{(\log\log m)^2}.
$$

Since $h(m)/\log m\to\infty$, eventually $\exp(a h(m))>9m^8$. Hence $N>m^2$, and the displayed inequality yields $N\ge9^{-1/4}\exp(a h(m)/4)\ge\exp(a h(m)/8)$ for all sufficiently large $m$. This proves the quantitative result with $b=a/8$, simultaneously for every $n\ge m$. For any fixed $c\ge1$, eventually $m\le m^c$ and $m^c+1<\exp(bh(m))$. Taking $n=m^c$ proves L-gct-011. The same argument excludes every $m\le n\le K m^c$ at once for each fixed $K,c$. [Theorem 1.1 and its gate model](https://github.com/openai/math/blob/92b516ef8e2abf66c3db7aa31438d3010bc7956f/preprints/Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026/build/intro.tex#L22-L51)

## Independent check using Laurent-series circuits

Remark N.6 of the November 23 paper explicitly identifies the polynomial-size complex orbit-closure conjecture of Mulmuley and Sohoni as a consequence of its Theorem N.5. The authors credit the determinant algorithm to Berkowitz and identify this remark as the part outside their Lean formalization. The following gives the topological transfer for pequalnp's definitions. [Theorem N.5 and Remark N.6, p. 64](https://github.com/anthropics/formal-math/blob/918c8e2778aee18b0283dc5a33ed39ab3cd63a96/vp-vnp/paper.pdf#page=64)

The November 23 result *VP ≠ VNP over every field* gives another proof of the qualitative separation. Its approximate-circuit theorem over $\mathbb C$ lower-bounds the size of a circuit over $\mathbb C((t))$ whose output is regular in every coefficient and specializes at $t=0$ to $\operatorname{per}_m$. The bound is $m^{d(\log_2m)^{1/3}}$ for some $d>0$, at every sufficiently large $m$. Its Lean statement explicitly allows arbitrary Laurent-series constants and counts input nodes as gates. [Theorem statement and circuit model](https://github.com/anthropics/formal-math/blob/918c8e2778aee18b0283dc5a33ed39ab3cd63a96/vp-vnp/Statement.lean#L20-L60) · [Lean proof](https://github.com/anthropics/formal-math/blob/918c8e2778aee18b0283dc5a33ed39ab3cd63a96/vp-vnp/Solution.lean#L38-L44)

Here one uses convergence of **all** coefficients of $q_j$. For fixed $m,N$, let $F$ be the polynomial map from the affine space of pencil coefficients to the affine space of output coefficients of degree at most $N$, given by taking the determinant. The limit $y=\operatorname{per}_m$ lies in the Zariski closure of the image. Compactify the source in projective space and take the closure of the graph in its product with the target. Projection to the target is proper, so the closed graph has a point over $y$. Algebraic curve selection through this point, with generic point in the original graph, followed by normalization and completion, gives a pencil over $\mathbb C((t))$. All determinant coefficients belong to $\mathbb C[[t]]$ and specialize to $y$. If $y$ is already in the image, a constant pencil suffices. Equivalently one can apply Bürgisser's semicontinuity theorem to the bounded straight-line computations of the $q_j$. [Bürgisser, *The Complexity of Factors of Multivariate Polynomials*, Theorem 2.4 and its proof](https://arxiv.org/pdf/1812.06828#page=10)

Compile that pencil by the same division-free algorithm. Scalar inputs and variables contribute only polynomially many gates in $N,m$, and subtraction can be implemented with a shared scalar $-1$, a multiplication and an addition. The resulting program satisfies the approximate-circuit theorem. If $N\le K m^c+1$, its size is polynomial in $m$, contradicting the stated lower bound for all sufficiently large $m$. This argument also gives L-gct-011 independently of the stronger numerical estimate above.

## Formal verification

The project-side Lean files prove dehomogenization, the passage to polynomial equations on degree-$m$ coefficients, the binary gate count, the quantitative bound on matrix order from Theorem 1.1, and the specialization to the exact quantifiers of L-gct-011. The final implication takes only the degree-component border-circuit lower bound of Theorem 1.1 over $\mathbb C$ as a hypothesis. The November 24 authors describe this bound as a paper result. The Laurent-series lower bound in the second argument has its own Lean proof and comparator check in its authors' environment. The transfer from complex limits to Laurent-series circuits in that second argument is given here on paper. [Dehomogenization and limits](data/gct-frontier/OrbitSeparation.lean) · [Circuit construction](data/gct-frontier/DetPencilCircuit.lean) · [Full reduction](data/gct-frontier/BorderCircuitTransfer.lean) · [November 24 formalization scope](https://github.com/openai/math/blob/92b516ef8e2abf66c3db7aa31438d3010bc7956f/lean/docs/379.md#hamiltonian-cycle-and-the-permanent) · [November 23 comparator run](https://github.com/anthropics/formal-math/actions/runs/45266217321/job/138013752301)

With the project's pinned Lean 4.36.0 toolchain, run the following commands from the repository's Lean directory.

~~~sh
lake build +PEqualNP.Gct.L001 +PEqualNP.Gct.L023 +PEqualNP.Gct.L074
lake env lean -R ../notes/data/gct-frontier -o .lake/build/lib/lean/OrbitSeparation.olean ../notes/data/gct-frontier/OrbitSeparation.lean
lake env lean -R ../notes/data/gct-frontier -o .lake/build/lib/lean/DetPencilCircuit.olean ../notes/data/gct-frontier/DetPencilCircuit.lean
lake env lean -R ../notes/data/gct-frontier ../notes/data/gct-frontier/BorderCircuitTransfer.lean
~~~

An additional audit type-checked the final implication against the literal project statement and inspected its axioms, together with those of the determinant circuit, degree-projection theorem and quantitative transfer. Lean reported only `propext`, `Classical.choice` and `Quot.sound`. The lower bound is visible in the type of the implication as a theorem argument.
