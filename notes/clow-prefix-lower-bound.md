# A supercubic lower bound for edge-labelled closed walks computing the permanent

**Theorem.** Let a length-$m$ layered program use the ordered closed walks of Mahajan and Vinay. Give every physical state an arbitrary number of complex coordinates. A transition traversing $i\to j$ multiplies its own arbitrary matrix by $x_{ij}$. If the permanent is a coefficientwise limit of these programs, their total internal-coordinate budget must be $\Omega(m^{7/2})$. For every $m\ge70$ a budget of $m^3$ internal coordinates is impossible. With at most three coordinates per state immediately after the second edge, the permanent is already excluded for every $m\ge21$, irrespective of all later widths. The results allow independently chosen matrices at every position, including the choice of next head. [Closed-walk model and its determinant pencil](closed-walk-moments.md) · [Mahajan and Vinay](https://scholar.lib.vt.edu/ejournals/CJTCS/cjtcs/articles/1997/5/cj97-05.pdf)

The usual layered graph pencil has size one plus its number of internal coordinates. This closes the proposed route to a size-$(m^3+1)$ determinant through this graph, including nonuniform widths and limits. L-gct-011 permits arbitrary linear substitutions into a determinant and its orbit closure. The argument below uses the prescribed variable on a traversed edge. The unrestricted $c=3$ instance remains open. [Project statement](https://data.pequalnp.com/data/lemma/L-gct-011.e0ee1c5dec3d.json) · [Earlier exponent results](mulmuley-sohoni-separation.md)

## What two steps can see

Number vertices $0,\ldots,m-1$. A closed walk starts at its least vertex, called its head, travels through vertices strictly larger than its head and ends on returning to the head. Successive heads increase. The first head is zero. At an intermediate position the physical state specifies the current head and vertex. Zero-width or deleted states can be treated as having zero transition weights.

Fix $s\ge1$. Choose disjoint nonroot sets $A,D$, with $s$ addresses in $A$ and $s^2$ columns in $D$. Suppose every state $(0,b)$, $b\in D$, has width at most $s-1$ immediately after the second edge. For $i\in A$, let $p_i^b\in\mathbb C^{s-1}$ be the vector associated to the two-edge prefix $0\to i\to b$, padding with zeros as necessary. This vector contains the initial weights and both transition matrices. All these prefixes with the same $b$ have the same possible continuations.

Put $x_{0i}=\lambda_i$ on $A$, and support row $i\in A$ only in $D$. All other entries of row zero vanish. The only two-step contributions are the open walks just described, since $x_{i0}=0$ for all $i\in A$. If
$$
\sum_{i\in A}\lambda_i x_{ib}p_i^b=0\qquad(b\in D),
$$
every cut vector vanishes and the output on this input is zero. We may choose all the other rows after solving these equations.

Suppose $B\subset D$ has $s$ elements and the address rows are supported on $B$ with entries $Y_{ib}$. For any $a\in A$, match the other $m-s-1$ rows bijectively by singleton entries of one to the columns outside $B\cup\{a\}$. Now column $a$ is available only to row zero. The full permanent is exactly $\lambda_a\operatorname{per}(Y_{A,B})$.

## A bounded witness for arbitrary prefix vectors

There is a constant $\delta_s>0$, depending only on $s$, such that for every collection of the vectors $p_i^b$ there is an input with all entries of absolute value at most one, all cut vectors zero and permanent of absolute value at least $\delta_s$.

First take generic prefix vectors. For every $b$ any $s-1$ of its $s$ vectors are independent. These conditions give a dense open set. For instance, the vectors on a moment curve at distinct parameters have every prescribed maximal minor nonzero by the Vandermonde formula. For $s=1$ the prefix space is zero and the single relation coordinate can be one. In either case take a relation $z_b$ with every coordinate nonzero. In the generic case its entries can be taken to be the signed maximal minors. Write $Z=(z_{ib})$.

**Balance the rows and columns.** Number the rows $1,\ldots,s$. Allocate the $s^2$ columns to the rows with quotas $1,3,\ldots,2s-1$, maximizing $\prod_b |z_{o(b),b}|$ over all allocations $o$. For a column owned by $i$ draw an edge from $i$ to each $j$ with weight $\log|z_{jb}/z_{ib}|$. Every simple directed cycle has nonpositive total weight. Reassigning its distinct owned columns around a positive cycle would improve the allocation while preserving the quotas. Hence the largest weight $v_j$ of a path to $j$ from an auxiliary source with zero edges to every row exists. Deleting cycles never decreases path weight. For each of the edges one has $v_j-v_i\ge\log|z_{jb}/z_{ib}|$.

Set $\alpha_i=e^{-v_i}$ and $\beta_b=1/(\alpha_{o(b)}|z_{o(b),b}|)$. The matrix $Y_{ib}=\alpha_i z_{ib}\beta_b$ has $|Y_{ib}|\le1$ and equality on every allocated entry. Let $\lambda_i=\alpha_i^{-1}/\max_j\alpha_j^{-1}$. Then $\max_i\lambda_i=1$, and for every $b$
$$
\sum_i\lambda_iY_{ib}p_i^b =
\frac{\beta_b}{\max_j\alpha_j^{-1}}\sum_i z_{ib}p_i^b=0.
$$

**Extract a permanent.** In any matrix whose $k$th row has at least $2k-1$ nonzero entries, some maximal square submatrix has nonzero permanent. This is Corollary L2 in Yang Yu's work. For completeness, consider the squarefree algebra $\mathbb C[t_b:b\in D]/(t_b^2:b\in D)$. Multiplication by a linear form with more than $2d$ nonzero coefficients is injective from degree $d$. To see this for nonzero coefficients on a set of size $n$, rescale those variables to coefficient one. On their squarefree monomial basis, multiplication by $U=\sum_b t_b$ has adjoint $V$ that deletes one variable in every possible way. On degree $e$ one has $VU-UV=(n-2e)I$. The terms exchanging two different variables cancel and the diagonal counts $n-e$ additions versus $e$ deletions. Thus $\|Uf\|^2=\|Vf\|^2+(n-2e)\|f\|^2$. With other variables present, decompose by their fixed monomials, so $e\le d$. Multiplying the row forms successively leaves a nonzero squarefree coefficient in degree $s$. Expansion identifies each such coefficient with the permanent on those $s$ columns. The Lean file gives a separate combinatorial induction for arbitrary complex weights. [Yu, Theorem L1 and Corollary L2](https://www.preprints.org/manuscript/202603.0035) · [Feinsilver on the Boolean lattice operators](https://arxiv.org/abs/1102.0368) · [Kirkup on maximal permanental ideals](https://arxiv.org/abs/math/0510025)

The matrices $Y$ in the closed unit polydisc with at least $2k-1$ unit-modulus entries in row $k$ form a compact set. The maximum absolute permanent of an $s$-column submatrix is continuous and positive throughout this set. Its minimum $\delta_s$ is therefore positive. Choose $B$ attaining the maximum, zero the unused columns, and choose $a$ with $\lambda_a=1$. The singleton completion gives the asserted input for generic prefix vectors.

For arbitrary prefix vectors take a sequence of generic ones tending to them. There are only finitely many $a,B$ and choices of singleton completion. Along a subsequence these choices are fixed and the bounded inputs converge. The cut equations are continuous in both the input and the prefix vectors, and the bound $|\operatorname{per}X|\ge\delta_s$ is closed. This produces a witness for the given vectors themselves, including those of deficient rank. Taking generic approximations here is an argument in the space of prefix data and requires no realization of those approximations by a program.

Finally, coefficientwise convergence of degree-$m$ polynomials implies uniform convergence on the unit polydisc. The supremum of their difference is bounded by the sum of absolute coefficient differences. Thus the same positive margin excludes border computation even when all underlying matrices may diverge.

## Moving the obstruction through the program

Write $q_{k,h,b}$ for the number of coordinates at the physical state $(h,b)$ just after edge $k$. For $1\le h\le t$ and $m-t\ge s^2+s+1$,
$$
 \#\{b>h:q_{t+2,h,b}\ge s\}\ \ge\ m-h-s^2. \tag{1}
$$
For $t=h=0$ the corresponding lower bound is $m-s^2$ whenever $m\ge s^2+s+1$.

Suppose instead there are $s^2$ narrow columns $b>h$. Reserve those columns and $s$ further vertices above $h$ as addresses. Choose $t$ spectator vertices containing all $0,\ldots,h-1$ and avoiding $h$ and all reserved vertices. The stated size inequality guarantees room for exactly $t-h$ further spectators. Retain just the edges of a fixed directed $t$-cycle starting at zero on the spectators, all edges inside the active complement, and no edges between the two sets.

Extract the coefficient of the product of the spectator edges, each to power one, and retain terms of degree one in active row $h$. This is a fixed linear operation on coefficients. On the permanent it yields the permanent of the active block. On the graph the initial walk has to traverse the prescribed spectator cycle once. Any later visit to a spectator would consume an extra spectator edge. The least active vertex is $h$, so a path using row $h$ must start its first active walk there. All active paths beginning at $h$ use row $h$ exactly once. Consequently the resulting active program starts with the fixed prefix, has $m-t$ edges left and reaches $(h,b)$ at original cut $t+2$ after its first two active edges. Apply the bounded witness on the active block. This contradicts coefficientwise convergence to its permanent and proves (1). For $t=h=0$ apply the original two-edge argument directly. Variable choices of widths under a fixed total budget cause no problem. For each fixed $m$ there are only finitely many dimension profiles, so a convergent sequence has a subsequence with a single profile.

**Count internal coordinates.** At each pair $(t,h)$, sum (1) over the positive integers $s$ allowed there. A state of width $q$ contributes to exactly $q$ positive width levels in the unrestricted sum, so these lower bounds can be added. Different pairs specify different layer and head. Put $T_s=m-s^2-s-1$. Adding the original head and the positive pairs gives
$$
 W(m)\ \ge\ \sum_{\substack{s\ge1\\ T_s\ge0}}
 \left[(m-s^2)\left(1+\binom{T_s+1}{2}\right)-\binom{T_s+2}{3}\right]. \tag{2}
$$

| $m$ | Lower bound in (2) | Cubic internal-coordinate budget |
|---:|---:|---:|
| 21 | 3,871 | 9,261 |
| 69 | 325,715 | 328,509 |
| 70 | **343,257** | **343,000** |
| 71 | 361,464 | 357,911 |
| 100 | 1,252,371 | 1,000,000 |

At $m=70$, levels $1$ through $7$ contribute $342{,}907$ away from the original head and another $350$ there. For all $m=71+x$, $x\ge0$, retain only the same seven levels and the positive pairs. Six times the excess over $m^3$ equals
$$
19176+20485x+759x^2+8x^3>0.
$$
For each level $s$ the count over positive pairs used here is $T_s(T_s+1)(2m-2s^2+s-1)/6$. This proves the stated cutoff, without assuming the bound is sharp below seventy.

For the growth rate, let $m\ge16$, $s=\lfloor\sqrt m/2\rfloor$, and $1\le h\le t\le\lfloor m/2\rfloor$. Then $m-t\ge s^2+s+1$, and at least $m/4$ states at each pair have width at least $s\ge\sqrt m/4$. There are at least $m^2/9$ pairs. Thus $W(m)\ge m^{7/2}/144$.

## Six-row tests

At six rows a general width-three program is still undecided. The two-step argument supplies twenty exact necessary conditions. For distinct four-element subsets $A,B$ of the five nonroot labels choose $a\in A\setminus B$. Let $z_b$ be the four signed maximal minors of the three-coordinate prefix vectors on $A$ for column $b$. The cut equations hold with $\lambda_i=1$, also if all these minors vanish. The singleton completion forces $\operatorname{per}([z_b]_{b\in B})=0$ in any exact realization. Each condition is a degree-twelve polynomial in prefix coordinates. These are conditions on the weights of an exact program.

For $A=\{1,2,3,4\}$, $B=\{2,3,4,5\}$ and $p_i^b=(1,i,i^2)$, take the relation $(-1,3,-3,1)$ in every column. The program evaluates to zero for every choice of subsequent weights. The integer input and its permanent are
$$
 X=\begin{pmatrix}
0&1&1&1&1&0\\
0&0&-1&-1&-1&-1\\
0&0&3&3&3&3\\
0&0&-3&-3&-3&-3\\
0&0&1&1&1&1\\
1&0&0&0&0&0
\end{pmatrix},\qquad \operatorname{per}X=4!(-1)(3)(-3)(1)=216 .
$$
This example still works if each state applies its own fixed linear map to those quadratic vectors.

There is a border test for every encoding $p_i^b=p_i G_b$ of dimension $q$. Set aside a nonroot label $r$ with row $r$ sent only to column zero. Let $A$ contain every other nonroot label. Test row zero equal to the coordinate vector $e_a$, and let all rows in $A$ have ones in nonroot columns except column $t$, with $a,t\in A$. Their entries in column zero are zero. The permanent grid on $(a,t)$ is $(m-2)!I_{m-2}$. Each suffix from the two-edge state uses no further entries of row zero. Hence column $t$ of the program grid has entries $p_a\cdot u_t$ for the same vector $u_t$ across all $a$. Grid rank is at most $q$ and cannot increase in a limit. Thus this class needs $q\ge m-2$, already four at six rows.

A different six-row test fixes the exact row-history program, pruned to prefixes and suffixes of permutation covers, and allows an arbitrary matrix at just one interior cut. A prefix with visited set $S$ and a suffix with complementary required set $T$ contribute the matrix entry indexed by their physical state and $(S,T)$. A genuine cover fixes each diagonal entry to one. For a nonmatching monomial, summing its surviving paths gives a homogeneous integer linear equation in the off-diagonal entries. Exhaustive enumeration gives the following ranks over $\mathbb F_{101}$.

| Cut after edge | Off-diagonal unknowns | Rank modulo 101 | Largest forced identity block |
|---:|---:|---:|---:|
| 2 | 72 | 72 | 4 |
| 3 | 210 | 210 | 6 |
| 4 | 110 | 110 | 4 |

Full column rank modulo a prime gives full column rank over $\mathbb C$. Each cut matrix is uniquely the identity on its histories. A fixed left inverse for the coefficient equations also forces convergence to these same blocks in a border sequence. A rank-three cut cannot approach any of the indicated identity blocks. Thus repairing the exact six-row history construction by changing a single one of these cuts cannot succeed.

## Verification

Lean checks weighted squarefree injectivity in every degree, existence of the nonzero squarefree coefficient, the uniform compact-family estimate, extension of closed witness relations from dense prefix data, the two-step kernel and row rescaling identities, exclusion of coefficientwise limits from a uniform bounded-input gap, the six-row input, and the arithmetic for all $m\ge70$. The allocation argument, the application to the closed-walk graph, and the reason the spectator projections count independent layer and head pairs are proved in the text. The Python checks use integer and rational arithmetic, enumerate all six-row path groups for the single-cut ranks, compare all paths under sixteen spectator projections, and verify a degenerating 21-row example whose full permanent tends to one. [Lean certificates](data/gct-frontier/ClowPrefix.lean) · [Reproducible computations](data/gct-frontier/clow_prefix.py)

From the repository root run the Python check. From the Lean directory run the certificate with the repository toolchain.

~~~sh
python notes/data/gct-frontier/clow_prefix.py
~~~

~~~sh
lake env lean ../notes/data/gct-frontier/ClowPrefix.lean
~~~
