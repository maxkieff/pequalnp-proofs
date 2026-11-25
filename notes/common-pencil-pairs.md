# Common determinant pencils for pairs of ten-row restrictions

Of the 55 pairs in the [eleven-restriction experiment](cubic-padding-experiments.md), 30 admit simultaneous coefficientwise approximation by affine determinants of size **987**. The same sequence of pencils works on both members of each such pair. Consequently no polynomial equation on those two outputs can separate their permanent data from the size-1,001 pencils. A single pencil also matches the Taylor coefficients through degree ten on both members. Exact equality in all degrees for a single pencil is a separate question.

Two bounds apply to the **unrestricted** ten-row permanent. A polynomial equation separating it from all size-1,001 affine determinants must have degree at least **231** in any linear observations of the output. Moreover, for **any 26,795 prescribed scalar linear observations**, one size-1,001 determinant matches all of their values exactly. Both results therefore apply to every pair and to the full collection of restrictions. The degree theorem is checked in Lean. The measurement bound follows from factoring the middle layer and a theorem on ranks of affine matrix spaces. The unrestricted ten-row containment and the eventual statement of L-gct-011 remain open. [Lean degree theorem](data/gct-frontier/PrunedPermanent.lean) · [de Seguins Pazzis](https://arxiv.org/abs/1102.4027) · [Project statement](https://data.pequalnp.com/data/lemma/L-gct-011.e0ee1c5dec3d.json)

## Identifying states in two different layers

Start with the subset program for the permanent. A state is the set of columns used so far. Step $k$ adds an unused column $j$, multiplying by $x_{ij}$ for the $k$th row $i$ in the chosen order. Its $2^{10}=1{,}024$ states give a size-1,023 determinant by taking the signed source-to-sink cofactor of $I$ minus the adjacency matrix. We will take the same cofactor after identifying some states. [Grenet’s construction](https://www-verimag.imag.fr/~grenetb/publis/Gre11.pdf)

Let the two masks delete triples in columns $c,d$, on disjoint sets of three rows. Read the first triple of rows first and the second triple last. At cut three select the 36 sets $S$ of size three containing $c$. At cut seven label a state by the three columns $Q$ still unused, and select the 36 labels containing $d$. Pair each $S$ with $Q=\rho(S)$, where $\rho$ interchanges $c,d$ and is the identity when $c=d$.

For a scalar $z\ne0$, multiply edges entering the selected late states by $z$ and edges leaving them by $z^{-1}$. Identify each paired early and late state, adding parallel edge weights. Every entry of the resulting matrix is affine in the input variables for fixed $z$. There are 988 states, hence the signed cofactor has size **987**. Padding by an identity block gives size 1,001.

Here is the cofactor calculation. Denote the selected early and late boundary vectors by $a$ (row) and $b$ (column). They contain the original path sums from the source to the early states and from the late states to the sink. In the original graph, decompose paths at the two cuts. Write

- $D$ for the sum over paths using unselected states at both cuts,
- $u$ for the row of transfers from the source through unselected early states to selected late states,
- $v$ for the column of transfers from selected early states through unselected late states to the sink,
- $K$ for the matrix of middle transfers between the two selected collections.

Thus the original permanent is $F=D+av+ub+aKb$. Eliminate all unpaired internal states in the folded graph. Their induced graph is acyclic, so the corresponding block of $I$ minus the adjacency matrix has determinant one and its inverse sums its paths. What remains is a direct term $D$, source and sink vectors $a+zu$ and $v+z^{-1}b$, and an internal block $I-zK$. Taking the bordered determinant gives the polynomial pencil output
$$
P_z=D\det(I-zK)+(a+zu)\operatorname{adj}(I-zK)(v+z^{-1}b).
$$
This identity holds even when $I-zK$ is singular. It can be obtained by replacing the sink row with the source coordinate vector before taking the cofactor, or by expanding the reduced bordered determinant.

On the first restriction, every path to a selected early state uses one of its three deleted entries, hence $a=0$. On the second, every suffix from a selected late state uses one of its three deleted entries, hence $b=0$. In each case the displayed expression has a polynomial extension to $z=0$, with value $F$. Taking $z=1/t$ for positive integers $t\to\infty$ gives the same coefficientwise limit on both restrictions. [Lean factorization and special-fibre identities](data/gct-frontier/CommonPencil.lean)

For the fixed pencil $P_1$, each entry of $K$ has degree four. The only possible degree-six term is $H=ab$. The degree-ten term is $F-\operatorname{tr}(K)H$, using $\operatorname{adj}(I-zK)=I+z(K-\operatorname{tr}(K)I)+O(z^2)$. All remaining terms have degree greater than ten. This proves exact agreement through degree ten on both masks. The specified swap pairing even has $\operatorname{tr}(K)=0$ since $S\cap\rho(S)\ne\varnothing$. A middle path needs disjoint selected and unused column sets.

## Which pairs can this identification handle?

The original masks $F_j$ use rows $j,j+1,j+2$ modulo ten in column $j$ for $0\le j<10$, and $F_{10}$ uses rows $3,4,5$ in column zero. The coordinate sets deleted by any two masks are disjoint. Their **row sets** can overlap.

The following table optimizes one identification between two cuts of the subset graph whose short term vanishes on both masks. It ranges over every row order, every pair of distinct internal cuts and arbitrary constant changes of boundary basis. The last column gives the size attained by this construction.

| Common rows | Same column? | Number of pairs | Maximum coordinates identified | Cofactor size |
|---:|:---:|---:|---:|---:|
| 0 | no | 29 | 36 | 987 |
| 0 | yes | 1 | 36 | 987 |
| 1 | no | 12 | 9 | 1,014 |
| 2 | no | 12 | 9 | 1,014 |
| 3 | no | 1 | 8 | 1,015 |

For the verification, choose nonempty disjoint prefix and suffix sets of rows, leaving at least one middle row. Label the boundary states by the sets $S,Q$ of used prefix columns and unused suffix columns. Let $L_S,R_Q$ be the corresponding small permanents. A rank-$r$ identification introduces a short term of the form $\sum W_{SQ} L_S R_Q$, with $W$ of rank $r$. Invertible changes of basis reduce a rank-$r$ pairing to $r$ coordinate identifications. On each mask the surviving products $L_SR_Q$ are linearly independent, since their column sets on the independent prefix and suffix row variables determine $S,Q$. The short term must vanish, so $W_{SQ}$ may be nonzero only if each of the two masks kills at least one of the two factors.

For a given mask, a prefix permanent is killed precisely when every prefix row belongs to its forbidden triple and the forbidden column lies in $S$. The suffix rule is identical with $Q$ in place of $S$. Partition each boundary into four types according to which masks kill its members. Types $u,v\subseteq\{1,2\}$ are compatible when $u\cup v=\{1,2\}$. The maximum rank is the maximum bipartite matching size in this support pattern. A maximum matching itself gives a partial permutation matrix $W$ attaining it. The cofactor calculation above applies to these selected coordinates. Its pole is the short term and the constant correction is minus that term times $\operatorname{tr}(K)$, so both vanish on the required pair even if different summands are killed on different sides.

The script enumerates disjoint row subsets and computes the minimum vertex cover of the four-type bipartite graph with its multiplicities. Reading columns instead gives no improvement. A single forbidden scanned row lies on at most one side, where it can kill at most three states, corresponding to subsets of its three forbidden columns. [Exact enumeration and full-pencil checks](data/gct-frontier/common_pencil.py)

## One pencil with just two error terms

For $F_0,F_{10}$ the two masks are in column zero. A selected early state has already used zero, while a selected late state still has zero unused. There is no middle path between them, so $K=0$. With the identity pairing on the 36 triples the entire unrestricted polynomial of the size-987 pencil is
$$
P_z(X)=z^{-1}H_6(X)+\operatorname{per}_{10}(X)+zH_{14}(X).
$$
Write $E,M,T$ for the first three, middle four and last three rows in the chosen order. For $S$ running through the triples containing column zero the two errors are
$$
H_6=\sum_S\operatorname{per}X_{E,S}\operatorname{per}X_{T,S},
\qquad
H_{14}=\sum_S\operatorname{per}X_{E\cup M,S^c}\operatorname{per}X_{M\cup T,S^c}.
$$
At the all-ones matrix these three coefficients are $1{,}296$, $3{,}628{,}800$ and $914{,}457{,}600$. On either mask $H_6$ vanishes identically. On the unrestricted space, removing either error within size 1,001 would suffice for ten-row border containment. If only the degree-14 error remains, dilate toward zero and extract the lowest component. If only the degree-six error remains, dilate toward infinity and extract the highest component. The size is preserved by scaling one determinant row. [Lean three-term identity](data/gct-frontier/CommonPencil.lean) · [Same-size homogenization to the project orbit closure](data/gct-frontier/CubicExamples.lean)

**Changing the identification.** An invertible matrix $G$ between the same two boundary spaces gives the two errors $aGb$ and $uG^{-1}v$, absorbing $z$ into $G$. Each entry of $G$ is readable from the degree-six output. Set the early and late rows to distinct coordinate vectors using prescribed triples $S,T'$. Each entry $(G^{-1})_{T',S}$ is likewise readable from degree fourteen. Choose four distinct middle columns $W$ outside $S\cup T'$ (there are at least five). Assign them once each to the middle rows. Assign the early rows to $(T')^c\setminus W$ and the late rows to $S^c\setminus W$. Each of the two seven-row permanents then singles out its prescribed complementary set and equals one there. Thus convergence of both errors to zero would require $G\to0$ and $G^{-1}\to0$, contrary to $GG^{-1}=I$.

This argument also permits arbitrary homogeneous linear changes of the 100 input variables and an output scalar in this repeated-column family. To see the scope of the claim, first consider a true symmetry $x_{ij}\mapsto r_i c_j x_{ij}$ of the permanent. The weights of the two readings just described multiply to $(\prod_i r_i\prod_j c_j)^2=1$. Hence the diagonal equations $\sum_{T'}G_{S,T'}(G^{-1})_{T',S}=1$ persist in the rescaled readings. Permutations and transposition can be held fixed along a subsequence. These generate the permanent’s linear stabilizer together with the torus scalings. [Marcus and May, The Permanent Function](https://doi.org/10.4153/CJM-1962-013-4)

For general input changes, normalize any nonzero output scalar by absorbing a tenth root into the linear input transformation; the opposite residual scalar weights on degrees six and fourteen are absorbed into $G,G^{-1}$. Convergence of the degree-ten component now gives $F\circ A_t\to F$ for $F=\operatorname{per}_{10}$. One may approximate singular $A_t$ by invertible matrices, term by term. The complex linear group orbit is a locally closed smooth manifold, and its orbit map has a local analytic section near $F$ taking $F$ to the identity. This also follows by restricting the orbit map to a complement of the stabilizer Lie algebra and using the inverse function theorem in orbit coordinates. Thus there exist $B_t\to I$ with $F\circ B_t=F\circ A_t$. Composing the converging outputs with $B_t^{-1}$ reduces to the stabilizers $A_t B_t^{-1}$. The reciprocal identities exclude convergence there. This proves the claim for the stated changes of variables. Translations of the input or independent modifications of pencil entries lie outside this argument.

**Computing either correction separately.** Both errors for the identity pairing have a smooth integer zero with a nonsingular Hessian in all their active variables. The script constructs the point by solving for one entry of a row, and evaluates the Hessian by complementary minors. The determinant residues are exact.

| Error | Active variables | Nonzero first derivative at the zero | Hessian determinant mod 1,009, up to row/column order | Border size lower bound |
|---|---:|---:|---:|---:|
| $H_6$ | 60 | 336 | 897 | 30 |
| $H_{14}$ | 90 | $-117{,}257{,}020{,}944$ | 975 | 45 |

At a smooth zero of a size-$n$ border determinant the Hessian rank is at most $2n$. Nearby zeros of approximating polynomials exist along a transverse line, and an invertible Hessian minor persists. Thus neither correction admits a standalone size-14 determinant. A correction that also uses coordinates of the original pencil is still possible. [Mignon–Ressayre](https://math.univ-lyon1.fr/~ressayre/PDFs/permdet.pdf) · [Landsberg–Manivel–Ressayre](https://arxiv.org/abs/1004.4802) · [Lean border-Hessian implication](data/gct-frontier/CommonPencil.lean) · [Exact derivative certificates](data/gct-frontier/common_pencil.py)

## A degree barrier for unrestricted separating equations

Let $\Phi$ be a polynomial in any collection of linear observations of a proposed output polynomial. Examples include its coefficients, coefficients after setting variables to zero on several restrictions, or its values on specified matrices. Suppose $\Phi$ vanishes for every size-1,001 affine determinant and is nonzero at the ten-row permanent.

At the central layer of the original subset program, attach a scalar $z_S$ to each of the $\binom{10}{5}=252$ states. A path crosses exactly one of them. The whole output $F_z$ depends linearly on $z$, and $F_{\mathbf 1}=\operatorname{per}_{10}$. With at most 230 nonzero scalars, delete the other central states. This gives an exact affine determinant of size at most $1{,}023-252+230=1{,}001$. It follows that $q(z)=\Phi(F_z)$ vanishes on every coordinate subspace of dimension 230, while $q(\mathbf 1)\ne0$.

Any monomial involving at most 230 distinct $z_S$ has zero coefficient in $q$. Set all coordinates outside its support to zero and compare coefficients with the zero polynomial on that subspace. Some monomial survives because $q(\mathbf 1)\ne0$. Consequently
$$
\deg\Phi\ \ge\ \deg q\ \ge\ 231 .
$$
The reasoning applies to every choice of the first five rows. In particular, for any such row choice, if a proposed list of individual matching coefficients touches at most 230 of the central five-column sets, one sparse central pencil reproduces all those coefficients while keeping every nonmatching coefficient zero. At the minimum degree 231 the pullback $q$ must be a linear combination of squarefree monomials of degree 231. [Lean proof including the determinant construction](data/gct-frontier/PrunedPermanent.lean)

## Matching 26,795 arbitrary linear measurements exactly

Split the rows into two ordered sets $E,T$ of five rows each. Index a $252\times252$ matrix $Z$ by five-column sets. Define $L_S=\operatorname{per}X_{E,S}$ and $R_U=\operatorname{per}X_{T,U^c}$. The polynomial
$$
F_Z=\sum_{S,U}L_S Z_{SU}R_U
$$
is linear in $Z$, and $F_I=\operatorname{per}_{10}$ by expansion across the cut. When $Z=AB$ has rank $r$, replace the 252 central states with $r$ states. If $P$ is a four-column state, its edge into state $a$ has weight $\sum_{j\notin P} x_{e j} A_{P\cup\{j\},a}$, where $e$ is the fifth row. The edge from $a$ to each six-column state $Q$ has weight $\sum_{j\in Q}B_{a,Q\setminus\{j\}} x_{tj}$, where $t$ is the sixth row. The remaining edges keep the original subset weights. The path sum is exactly $F_Z$. All edge weights are linear, and the signed cofactor has size $1{,}023-252+r=771+r$. Every rank-$230$ or lower transfer therefore gives an exact size-1,001 affine determinant after padding. The program checks a nondiagonal transfer of rank exactly 230 on the full cofactor. [Explicit cofactor verification](data/gct-frontier/common_pencil.py)

Now prescribe $k$ complex-linear scalar observations $\ell_i$ of the output. Coefficients, specified point values and derivatives at fixed points are examples. The matrices $Z$ satisfying $\ell_i(F_Z)=\ell_i(F_I)$ form a nonempty affine space of codimension at most $k$. An affine space of complex matrices of minimum rank $r$ has codimension at least $r(r+1)/2$. Since $231\cdot232/2=26{,}796$, any list of at most **26,795** observations has an exact match of rank at most 230, hence a single size-1,001 determinant matching the entire list. The pencil can depend on the list. More precisely, it suffices that the observations have rank at most 26,795 on the family $Z\mapsto F_Z$. The same result holds for observations of the degree-1,001 padded forms by composing each observation with multiplication by the fixed padding monomial and homogenizing the affine pencil. [de Seguins Pazzis, Large affine spaces of matrices with rank bounded below](https://arxiv.org/abs/1102.4027)

Here is a proof of the rank bound over $\mathbb C$. Choose a minimum-rank point and put it in the form $\operatorname{diag}(I_r,0)$ by row and column changes. The directions of the affine space supported in its leading $r\times r$ block form a subspace $\mathcal N$ of dimension at least $r^2-k$, for ambient codimension $k$. Every element of $\mathcal N$ is nilpotent. A nonzero eigenvalue would let a scalar multiple of that direction cancel an eigenvalue of $I_r$ and lower the rank.

For completeness, $\dim\mathcal N\le r(r-1)/2$ follows by induction. For $r=0$ this is immediate. Fix $v\ne0$ and put $q=\dim\mathcal N v$. Then $v\notin\mathcal N v$ by nilpotence. The operators in $\mathcal N$ that kill $v$ induce a nilpotent subspace on $\mathbb C^r/\mathbb Cv$. The kernel of this induced action consists of maps $v\otimes f$ with $f(v)=0$. For $A,B\in\mathcal N$, polarizing $\operatorname{tr}(A^2)=0$ gives $\operatorname{tr}(AB)=0$. In particular $f(Av)=0$ for each such kernel element and all $A\in\mathcal N$. These $f$ therefore span at most $r-q-1$ dimensions. By rank-nullity and induction, $\dim\mathcal N\le q+(r-1)(r-2)/2+(r-q-1)=r(r-1)/2$. Combining the bounds on $\dim\mathcal N$ gives $k\ge r(r+1)/2$.

The measurement count is sharp for this particular central family. A single monomial coefficient recovers each $Z_{SU}$ by assigning the early rows bijectively to $S$ and the late rows to $U^c$. Read the on- and above-diagonal entries of a principal $231\times231$ block. Matching these 26,796 readings to $I$ forces that block to be triangular with unit diagonal, hence forces rank at least 231. Yet the size-ten column-product determinant below passes every one of those readings. Likewise, on any one of the eleven masks each $L_S$ and $R_U$ has a surviving matching, since at most three of the five rows forbid a single column. Their products have disjoint monomial supports for different $(S,U)$. Fitting an entire mask inside this central family forces $Z=I$, even though that same mask admits an exact size-977 pencil by another construction. [Size-977 construction](data/gct-frontier/PrunedPermanent.lean)

A second test constrains which coefficients an equation must see. The size-ten diagonal determinant $\prod_j(\sum_i x_{ij})$ reproduces the permanent on every monomial except those using each column once and repeating a row. Transposing gives the other orientation. Hence a separating equation needs access to errors of both orientations when expressed in individual coefficient coordinates. A matrix of coefficients taking one input from each row cannot suffice, even if it has thousands of entries.

For the adjacent pair $F_0,F_1$, one identification saves at most nine states and gives size 1,014. Finding thirteen more savings there, or finding an equation of degree at least 231 that holds for every size-1,001 pencil and fails on the pair, remains open. The asymptotic result follows separately from the November circuit lower bounds. Their unspecified threshold leaves the ten-row case open. [Proof for all sufficiently large orders](gct-011-border-circuit-proof.md)

## Verification

The Lean files check the unrestricted degree-231 theorem end to end, including its sparse determinant realizations. They also check the two factor cancellations, the repeated-column identity, the boundary permanent zero, the state counts and the smooth-zero Hessian implication. The 26,795-measurement theorem, the reduction of the folded cofactor and the stabilizer argument are paper proofs. The Python program checks the 55-pair classification, constructs the signed size-987 cofactors, compares their determinants modulo 1,009 with an independently computed reduced matrix at two parameter values, checks the nondiagonal size-1,001 construction and verifies the integer Hessian certificates. All these calculations use exact arithmetic.

From the repository root run the following check.

~~~sh
python notes/data/gct-frontier/common_pencil.py
~~~

From the Lean directory run the two certificates.

~~~sh
lake env lean ../notes/data/gct-frontier/PrunedPermanent.lean
lake env lean ../notes/data/gct-frontier/CommonPencil.lean
~~~
