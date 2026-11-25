# The first two exponents of Mulmuley–Sohoni separation

**November 25 update.** The November 23 and 24 circuit lower bounds give the full asymptotic separation for every fixed exponent. The quadratic proof below records what follows from the project's earlier lower bound alone. [Proof for all exponents and formalization status](gct-011-border-circuit-proof.md)

The project asks whether, for every fixed positive integer $c$ and all sufficiently large $m$, the padded permanent lies outside the orbit closure of the complex determinant of size $m^c+1$. The Lean argument from L-gct-074 establishes the statement for $c=1,2$. It also gives a uniform result for all determinant sizes up to a fixed multiple of $m^2$ plus one. The first exponent beyond that argument is $c=3$. [Project statement](https://data.pequalnp.com/data/lemma/L-gct-011.e0ee1c5dec3d.json) · [Mulmuley and Sohoni](https://doi.org/10.1137/S009753970038715X)

## From a border expression to an orbit exclusion

Write $N=n+1$ and assume $m\le n$. The polynomial in the project is $z^{N-m}\operatorname{per}_m(X)$, with $z$ at position $(0,0)$ and $X$ in a disjoint $m$ by $m$ block. If this polynomial belongs to the determinant orbit closure, take a sequence of determinants after invertible linear substitutions converging coefficientwise to it. In every term set $z=1$, retain $X$, and set the remaining variables to zero. This fixed affine substitution preserves the determinant size and coefficientwise convergence. Its limit is $\operatorname{per}_m(X)$. Thus containment gives a border affine determinant expression of size **exactly $N$**. [Lean proof](data/gct-frontier/OrbitSeparation.lean) · [Project substitution theorem L-gct-023](../lean/PEqualNP/Gct/L023.lean)

For every fixed $K$, project theorem L-gct-074 makes every border expression of $\operatorname{per}_m$ at least $(K+2)m^2$ for all sufficiently large $m$. This contradicts $N=n+1$ whenever $m\le n\le Km^2$. Taking $K=1$ gives the two stated exponents, with one threshold for both. The complexity lower bound used here was already proved by the project. [L-gct-074](../lean/PEqualNP/Gct/L074.lean) · [Orbit exclusion and exponent theorems](data/gct-frontier/OrbitSeparation.lean)

A September 2026 result gives $N\ge m^3/(5{,}529{,}600e)$ for $m\ge1408$. The same substitution therefore excludes every admissible $N$ strictly below that threshold, including any $N=o(m^3)$ eventually. The $c=3$ instance asks for exclusion at $N=m^3+1$. The cubic estimate is a published input to this comparison. The Lean proof above uses L-gct-074. [Authors' theorem and formalization scope](https://raw.githubusercontent.com/openai/math/main/lean/docs/108.md)

## How much can a smooth Taylor component detect?

Let $F(x)=\operatorname{per}_m(B+A(x))$ for a linear matrix-valued map $A$ on $\mathbb C^d$. Let $G$ be the homogeneous degree-$r$ Taylor component at the origin, with $2\le r\le m$. Translation of the origin is absorbed into $B$. Suppose the common zero set of the first partials of $G$ is $\{0\}$. Then every $v\ne0$ has at least $r-1$ nonzero entries of $A(v)$ in distinct rows and distinct columns. In particular,

$$
d\le m(m-r+2),\qquad 4(r-1)(d-1)\le m(m+1)^2.
$$

To prove the matching condition, suppose every permutation of the columns meets at most $r-2$ nonzero entries of $A(v)$. In its product in the permanent, at most $r-2$ affine factors vary along $x=tv$. Differentiating with respect to any $x_j$ replaces one factor by a constant. The resulting univariate polynomial has degree at most $r-2$. Its coefficient of $t^{r-1}$ after summing over permutations is $\partial_jG(v)$. Thus $\nabla G(v)=0$. [Lean proof of the matching condition](data/gct-frontier/SmoothSliceCap.lean)

Now discard any $r-2$ columns of $A(v)$. The remaining $m(m-r+2)$ entries determine $v$ injectively, since a vector in their common kernel cannot supply the required matching. This gives the first inequality. Apply $4ab\le(a+b)^2$ to $a=r-1$ and $b=m-r+2$ to obtain the second. The degree-two dimension bound is sharp for Taylor components. At the all-ones matrix the Hessian of the permanent is $(m-2)!(J-I)\otimes(J-I)$, where $J$ is the $m$ by $m$ all-ones matrix. This is invertible for $m\ge2$, so the quadratic Taylor component is smooth in all $m^2$ variables. [Lean dimension and numerator bounds](data/gct-frontier/SmoothSliceCap.lean)

There is also a more precise geometric interpretation. For a direction $v$ and a coordinate direction $e_j$, extract $st^{r-1}$ from $\operatorname{per}(B+tA(v)+sA(e_j))$. Group terms by the $r-1$ rows and columns supplying $t$. Each group contains the permanent of the corresponding $(r-1)$ by $(r-1)$ submatrix of $A(v)$ as a factor, since the bijections on the complementary rows and columns can be chosen independently. The coefficient equals $\partial_jG(v)$. Thus $A(v)$ has a nonzero such subpermanent for every $v\ne0$. This expansion and the Hessian example are paper arguments. The Lean file proves the matching condition and both numerical inequalities. [Permanental varieties studied by Boralevi, Carlini, Michałek and Ventura](https://arxiv.org/abs/2402.17839)

For a homogeneous smooth restriction the project’s polar estimate gives $N\ge(r-1)(d-1)/11$. Its right-hand side is at most $m(m+1)^2/44$ for every choice of restriction. Even maximizing this particular certificate leaves it below $m^3+1$. The dimension bound also applies to smooth initial forms. Sheshadri proves a broader asymptotic ceiling for the polar comparisons in his Section 6, including comparisons that involve singular strata. [L-gct-024](../lean/PEqualNP/Gct/L024.lean) · [Sheshadri, *Smooth slices and the limits of determinantal lower bounds*](https://eccc.weizmann.ac.il/report/2026/275/)

## Testing many row choices together

Split the rows of a $2k$ by $2k$ matrix into two sets, one row from each of $k$ two-row blocks. For $a,b\in\{0,1\}^k$, the first row of block $i$ is the standard basis vector at column $a_i$ within the block. The second is the basis vector at column $1-b_i$. All entries outside the blocks are zero. If $a=b$, the result is a permutation matrix. If $a\ne b$, some column is zero. Consequently the $2^k$ by $2^k$ matrix of permanent values is the identity. On exactly the same inputs the determinant values form a diagonal matrix with entries $\pm1$.

Both matrices require width at least $2^k$ in any factorization across the two row groups, even in an entrywise limit. Every product of inner dimension below $2^k$ is singular, and the determinant is continuous. In fact, **one fixed linear substitution reproduces every permanent value on the entire grid**. Negate the top right entry of each two-row block and take the determinant. In each block this changes $ad-bc$ into $ad+bc$. The determinant of the block diagonal matrix is the product of the block determinants. Hence even retaining the joint values of all $4^k$ evaluations leaves this size-$2k$ determinant expression available. [Lean construction, signed substitution and border-width theorem](data/gct-frontier/RowEvaluation.lean)

Overlapping three-row matchings expose the first failure of this signing strategy. To match the permanent on all six permutation matrices of order three, the three even permutations need products of entrywise scaling factors equal to $1$ and the three odd permutations need products equal to $-1$. Multiplying each triple uses each of the nine factors exactly once. This would give $1=-1$ over $\mathbb C$. This certificate rules out every entrywise rescaling of a three-by-three determinant. L-gct-011 allows larger determinants whose entries can mix all input variables. [Lean certificate](data/gct-frontier/RowEvaluation.lean) · [The project’s two-by-two signing](../lean/PEqualNP/Gct/L004.lean)

Other restrictions on possible witnesses are known. Bürgisser, Ikenmeyer and Panova rule out occurrence obstructions for sufficiently large polynomial padding. Multiplicity comparisons remain possible. Efremenko, Landsberg, Schenck and Weyman prove that shifted partial derivative dimensions alone cannot separate the padded permanent from $\det_N$ for $N>2m^2+2m$. Neither result decides the orbit containment in L-gct-011. [Bürgisser–Ikenmeyer–Panova](https://arxiv.org/abs/1604.06431) · [Efremenko–Landsberg–Schenck–Weyman](https://arxiv.org/abs/1609.02103)

## Reproducing the formal checks

From the repository’s `lean` directory, with its pinned Lean 4.36.0 toolchain, run the following commands.

```sh
lake build +PEqualNP.Gct.L001 +PEqualNP.Gct.L023 +PEqualNP.Gct.L074 +PEqualNP.Gct.Helpers.OrbitClosure
lake env lean ../notes/data/gct-frontier/OrbitSeparation.lean
lake env lean ../notes/data/gct-frontier/SmoothSliceCap.lean
lake env lean ../notes/data/gct-frontier/RowEvaluation.lean
```
