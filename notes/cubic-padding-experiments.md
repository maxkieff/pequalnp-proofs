# Eleven tests at cubic padding

At exponent three, L-gct-011 asks whether the padded permanent eventually leaves the orbit closure of the determinant of size $N=m^3+1$. The full permanent belongs to that closure at every $m$ from 1 through 9. At $m=10$ the target is 1,001. The examples below give eleven restrictions with exact determinant size **at most 977** apiece. A single size-1,001 affine pencil fitting all eleven would put the full padded permanent in the project’s orbit closure at $m=10$. The existence of such a common pencil remains unresolved here. [Project statement](https://data.pequalnp.com/data/lemma/L-gct-011.e0ee1c5dec3d.json) · [Lean orbit and interpolation theorems](data/gct-frontier/CubicExamples.lean)

## Where the finite examples change

| Permanent size $m$ | Determinant supplied by the subset construction | Cubic target $m^3+1$ |
|---:|---:|---:|
| 3 | 7 | 28 |
| 8 | 255 | 513 |
| 9 | 511 | 730 |
| 10 | 1,023 | 1,001 |
| 11 | 2,047 | 1,332 |

Grenet’s construction uses a state for each set of columns already assigned to the first rows. Its weighted source-to-sink path sum is the permanent. With states in layer order, its adjacency matrix $T$ is strictly upper triangular. Thus $\det(I-T)=1$ and the appropriate signed cofactor of $I-T$ is the path sum. With $V$ states the cofactor has size $V-1$. For full support $V=2^m$. Padding the affine expression by an identity block and applying project lemma L-gct-006 gives the first nine orbit containments. The first crossing in the table concerns this construction. [Grenet’s paper](https://www-verimag.imag.fr/~grenetb/publis/Gre11.pdf) · [Project L-gct-007](../lean/PEqualNP/Gct/L007.lean) · [Checked small instances](data/gct-frontier/CubicExamples.lean)

For a $10\times10$ matrix, put three zeros in one column and read their rows first. At layers 1, 2, 3, the distinguished column cannot have been used. This removes respectively $1,9,36$ states. All later layers are fully reachable when the other entries are free. The cofactor size drops from 1,023 to **977**. Independent row and column permutations give the same bound for every such triple. Lean checks the symbolic determinant representation for arbitrary affine entries in all other positions. [Lean proof of the size-977 representation](data/gct-frontier/PrunedPermanent.lean)

As a comparison, allowing only entries with $|i-j|\le2$ gives layer sizes $1,3,6,6,6,6,6,6,6,3,1$ at $m=10$, hence a size-49 cofactor. At an interior cut after $k$ rows, the first $k-2$ columns are forced, and two of the next four must be used. Matching the selected columns in increasing order within each row group realizes all six choices. This gives size $6m-11$ for $m\ge4$. On a signed integer example the size-49 determinant and the ten-row permanent both evaluated to 681,750 by independent algorithms. [Reproducible computations](data/gct-frontier/cubic_support_examples.py)

## What eleven overlapping restrictions determine

Number rows and columns from 0 to 9. For each column $j$, let $F_j$ consist of its entries in rows $j,j+1,j+2$ modulo 10. Let $F_{10}$ consist of entries in rows 3, 4, 5 of column 0. Restriction $i$ sets the three entries in $F_i$ to zero. The eleven deleted triples are pairwise disjoint.

The first ten restrictions collectively miss **125 of the $10!$ matching monomials**, including the main diagonal. To count them, take the permanent of the zero-one matrix whose allowed entries in column $j$ are precisely $F_j$. The eleventh restriction reveals all 125. More generally, every monomial of total degree at most ten avoids at least one of the eleven triples. Its coefficient survives on that restriction. Eleven is sharp for recovering arbitrary Taylor polynomials through degree ten by proper coordinate subspaces. For any ten such subspaces, choose one coordinate set to zero on each. The product of those ten variables vanishes on their union. [Exact count and masks](data/gct-frontier/cubic_support_examples.py) · [Lean disjointness and common-pencil theorem](data/gct-frontier/CubicExamples.lean)

The local constructions even prefer different row orders. Of the 120 choices of three rows in a fixed column, exactly two bring the cofactor below 1,001 in a fixed row order. They are the first three and the last three. The experiment uses ten distinct cyclic row triples, with one repeated in another column. Five orders suffice by pairing the row triples starting at $j$ and $j+5$, for $0\le j<5$, and placing the pair at the two ends. This is the minimum for these local subset constructions. [Exhaustive row-order calculation](data/gct-frontier/cubic_support_examples.py)

The size-977 phenomenon has a precise range. For a single triple at any $m\ge4$, write $a,b$ for the numbers of consecutive forbidden rows at the two ends of the chosen order. A cut after $k$ rows loses a subset containing the distinguished column precisely when $k\le a$. It loses a subset omitting that column precisely when $m-k\le b$. Thus the cofactor size is $2^m-1-f_m(a)-f_m(b)$, where $f_m(t)=\sum_{j=0}^{t-1}\binom{m-1}{j}$. Since $a+b\le3$ and the first three increments of $f_m$ are nondecreasing, putting all three rows at one end minimizes this size. Every live subset at a cut gives a prefix and a suffix matching on complementary columns. Pairing each such prefix with each suffix gives an identity matrix of permanent values. The rank argument in the next paragraph therefore proves optimality for all one-row-per-layer programs, including limits, on this single restriction. At $m=11$ even its optimal row-ordered cofactor has size **1,991** against a target of **1,332**. At $m=12$ the corresponding sizes are 4,028 and 1,729. For unrestricted pencils each of these one-column restrictions contains a copy of the full $(m-1)$-row permanent. Set an allowed entry of the distinguished column to one and set the remaining entries in its row and column to zero. [Enumeration of all triple positions at six sizes](data/gct-frontier/cubic_support_examples.py)

There is a stronger obstruction for a **single branching program that reads one row per layer**. Cut it after row $k$. Index the first group of rows by a $k$-subset $S$ of columns and set these rows to the standard basis vectors for $S$ in order. Independently set the remaining rows to the basis vectors for the complement of a $k$-subset $T$. The permanent of this input is $\mathbf1_{S=T}$. Each input uses exactly ten entries, so it belongs to at least one of the eleven restrictions. The program’s evaluation matrix factors through the vertices at this cut, by summing over the vertex where the two parts of a path join. The identity matrix on $k$-subsets forces at least $\binom{10}{k}$ vertices there. Its full-rank minor gives the same conclusion under pointwise limits. Summing over the eleven layers gives **1,024 vertices**, or a size-1,023 cofactor. The complete subset program attains equality. Varying the order and widths along a bounded-size sequence does not evade the bound, since there are only finitely many choices and one occurs along an infinite subsequence. The script checks all 184,756 input pairs across these cuts. This paper argument confines any improvement to representations outside this row-ordered cofactor model. [Computed rank certificates](data/gct-frontier/cubic_support_examples.py) · [Nisan’s branching-program rank method](https://doi.org/10.1145/103418.103462)

Suppose a **single** affine determinant $D(X)$ of size $N$ agrees exactly with the permanent on every restriction. Its coefficients through degree ten agree globally. Consequently $t^{-10}D(tX)$ tends coefficientwise to $\operatorname{per}_{10}$ as $t\to0$. Scaling one row absorbs the factor $t^{-10}$ without changing determinant size. Homogenization into the project’s padded orbit closure also preserves size. In the Lean proof, homogenization at fixed degree is a finite linear map on coefficients, so it commutes with limits even if the coefficients of the underlying pencils diverge. [Checked same-size degeneration and homogenization](data/gct-frontier/CubicExamples.lean)

## A determinant that passes thousands of tests

Let $\Delta_m$ be the set of nonnegative integer $m\times m$ matrices whose entries sum to at most $m$. Its only members with nonzero permanent are the $m!$ permutation matrices. Consider the size-$2m$ diagonal determinant

$$
Q(X)=\prod_i\Big(\sum_j X_{ij}\Big)\prod_j\Big(\sum_i X_{ij}\Big).
$$

Every other matrix in $\Delta_m$ has a zero row or a zero column, so $Q$ agrees with the permanent on the entire simplex. Exact enumeration gave the following counts.

| $m$ | Inputs in $\Delta_m$ | Nonzero permanents | Disagreements at $A$ | Disagreements at $2A$ |
|---:|---:|---:|---:|---:|
| 2 | 15 | 2 | 0 | 2 |
| 3 | 220 | 6 | 0 | 6 |
| 4 | 4,845 | 24 | 0 | 24 |
| 5 | 142,506 | 120 | 0 | 120 |

At $2I_4$ the permanent is 16 and $Q$ is 256. A ninth diagonal entry $(31-15R_1(X))/16$, with $R_1$ the first row sum, repairs all 24 failures and preserves agreement on the original simplex. At $3I_4$ this adjusted determinant gives $-45927/8$ while the permanent gives 81. [Exact arithmetic and both sample checks](data/gct-frontier/cubic_support_examples.py)

Sheshadri’s November 2026 preprint reports exact determinantal complexity 15 for the full four-by-four permanent. Its lower-bound proof uses a normal form at a zero of the permanent and analyzes linear spaces in the singular locus. [Preprint and certificates](https://arxiv.org/abs/2611.06658v2)

The construction works for any $L\ge1$ distinct nonzero complex scales. Interpolate $t^{-m}$ at those scales by a univariate $h$ of degree at most $L-1$. Then $Q(X)h(R_1(X))$ agrees with the permanent at every scaled simplex point. Over $\mathbb C$, factor $h$ into affine linear factors to realize the product by a diagonal determinant of size at most $2m+L-1$. All its terms have degree at least $2m$. At $m=10$ a size-1,001 diagonal determinant can therefore pass **982 chosen scales** at every matrix in the $46{,}897{,}636{,}623{,}981$-point simplex while having zero degree-ten component. This bound concerns these particular samples.

Taking Taylor coefficients repairs the test. If one pencil $D$ satisfies $[t^j]D(tA)=[t^j]\operatorname{per}_m(tA)$ for every $A\in\Delta_m$ and $0\le j\le m$, each homogeneous component of their difference through degree $m$ vanishes on $\Delta_m$. To see why it vanishes globally, take a maximal-degree monomial $x^\alpha$ of any nonzero polynomial of degree at most $m$. Alon’s Combinatorial Nullstellensatz supplies a nonzero evaluation on the grid $\prod_i\{0,\ldots,\alpha_i\}$, entirely contained in the simplex. The same-size degeneration then applies. For a pencil of size $N$, its ray polynomial has degree at most $N$, so $N+1$ distinct scalar evaluations per direction suffice to recover the ray coefficients by interpolation. [Alon’s theorem](https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/abs/combinatorial-nullstellensatz/E32C7ED059D6B92C6C67E18CC716872A) · [Lean sparse-ray criterion](data/gct-frontier/CubicExamples.lean)

## The common-pencil problem

For the eleven restrictions, let $I_i$ be generated by the three variables in $F_i$. Disjointness gives $\bigcap_i I_i=\prod_i I_i$ by checking monomials. The first generators have degree 11 and there are $3^{11}=177{,}147$ of them. The concrete completion problem is to find a single affine pencil whose determinant equals $\operatorname{per}_{10}$ modulo this ideal. A solution gives orbit containment at size 1,001. For a separation certificate one would have to exclude simultaneous **limits** of pencils on the restrictions. Failure of exact fitting alone leaves that possibility open. The full conjecture also requires control as $m$ grows. [Project definition of the orbit closure](../lean/PEqualNP/Defs/Gct.lean)

The examples single out the corank of the pencil’s constant matrix as a parameter. For an exact fit, the initial form at the origin is the permanent. If that constant matrix has corank $r$, put it in the form $\operatorname{diag}(I,0_r)$ by constant row and column operations. The determinant has order at least $r$, and its degree-$r$ component is, up to a nonzero scalar, the determinant of the $r\times r$ bottom-right matrix of linear forms. Thus $r>m$ is impossible. For $r=m\ge3$, this would give an exact size-$m$ determinant for the permanent. The project’s border lower bound would then imply $m^2\le2m$, impossible for $m\ge3$. For the ten-row permanent an exact fit therefore has constant-matrix corank between 1 and 9. [Project L-gct-010](../lean/PEqualNP/Gct/L010.lean)

The local cofactor pencils have corank one. Write a normalized corank-one pencil as $\left(\begin{smallmatrix}I-T(X)&b(X)\\-c(X)&d(X)\end{smallmatrix}\right)$ with linear blocks. For $m=10$ the prescribed Taylor coefficients force $d=0$, $cT^jb=0$ for $0\le j<8$, and $cT^8b=\operatorname{per}_{10}$ after scalar normalization. This follows by expanding the Schur complement and using the vanishing of each lower coefficient in turn. Conversely, these identities suffice for the determinant to have the required initial form. Higher terms can be removed by dilation. On the signed size-49 example the first eight scalar moments vanish and the eighth-power moment is 681,750. The next system to investigate is a common choice of linear $T,b,c$ across the eleven restrictions, allowing variables from different rows in the same block. Since each prescribed moment has degree at most ten, its values on those restrictions determine it globally. The corank reduction, rank argument and finite-scale interpolation example are paper arguments. [Moment computation](data/gct-frontier/cubic_support_examples.py) · [Lean initial-form theorem](data/gct-frontier/CubicExamples.lean)

Thirty of the 55 pairs of restrictions admit simultaneous size-987 border pencils. Any polynomial equation separating the ten-row permanent from size-1,001 pencils must have degree at least 231. For any list of at most 26,795 scalar linear observations, one size-1,001 pencil matches the permanent on that entire list. [Common pencils for pairs of restrictions](common-pencil-pairs.md)

The computations use only Python’s standard library. Run `python notes/data/gct-frontier/cubic_support_examples.py` from the repository root. For Lean, run the following from `lean/` with the pinned 4.36.0 toolchain.

```sh
lake build +PEqualNP.Gct.L002 +PEqualNP.Gct.L006 +PEqualNP.Gct.L007 +PEqualNP.Gct.L010 +PEqualNP.Gct.Helpers.BorderSubst +PEqualNP.Gct.Helpers.Pointwise
lake env lean ../notes/data/gct-frontier/CubicExamples.lean
lake env lean ../notes/data/gct-frontier/PrunedPermanent.lean
```
