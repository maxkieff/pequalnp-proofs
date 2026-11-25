# Row-mixing pencils at cubic padding

For the ten-row permanent, the cubic instance of L-gct-011 asks about the orbit closure of a size-1,001 determinant. A corank-one construction can reach it by finding homogeneous linear blocks $c,T,b$ on at most 1,000 internal states with $cT^jb=0$ for $0\le j<8$ and $cT^8b=\operatorname{per}_{10}$. The determinant of the block pencil with rows $(I-T,b)$ and $(-c,0)$ then has the permanent as its initial form. Dilation and homogenization put the padded permanent in the same-size orbit closure. This would settle one finite containment. The project conjecture concerns eventual separation. [Previous Lean reduction](data/gct-frontier/CubicExamples.lean) · [Project statement](https://data.pequalnp.com/data/lemma/L-gct-011.e0ee1c5dec3d.json)

I tested a family of pencils built from the closed walks in Mahajan and Vinay’s determinant algorithm. Changing the signs on interior loops computes the full permanent through three rows. At four rows the first failures give a homogeneous sextic in the output coefficients. It is zero for every scalar weighting of this graph, even with a different weight on every transition in every layer, and is $-4$ for the permanent. Two internal coordinates per walk state suffice at four rows. At ten rows I constructed a size-972 pencil with four possible row-sum residues. It gets every permutation monomial’s coefficient right and has a specific unwanted coefficient of 2. [Checked four-row obstruction](data/gct-frontier/ClowMoments.lean) · [Computations](data/gct-frontier/clow_moments.py)

## A signed construction and its first errors

Number vertices from zero. A closed walk here starts at its head $h$, uses only vertices strictly larger than $h$ in its interior, and returns to $h$ once at the end. Take a sequence of such walks with strictly increasing heads, first head zero, and $m$ edges in total. Its monomial is the product of $x_{uv}$ over the traversed arcs $u\to v$. Every permutation monomial has exactly one sequence, obtained by writing its cycles in order of their minima. Other monomials can have several sequences. Weighting each closing arc by $-1$ gives $(-1)^m\det X$ by Mahajan and Vinay’s cancellation. [Original closed-walk construction](https://scholar.lib.vt.edu/ejournals/CJTCS/cjtcs/articles/1997/5/cj97-05.pdf)

I instead gave weight $-1$ to a loop $u\to u$ occurring inside a walk with head $h<u$, and weight $+1$ to all other arcs. This preserves coefficient one on every permutation in every size. I enumerated all legal sequences and grouped them by their commutative monomial.

| Rows | Sequences starting at zero | Distinct monomials | Coefficients different from the permanent |
|---:|---:|---:|---:|
| 2 | 2 | 2 | 0 |
| 3 | 10 | 8 | 0 |
| 4 | 84 | 54 | 6 |
| 5 | 956 | 502 | 128 |
| 6 | 13,630 | 5,815 | 2,120 |

At four rows the six residual monomials each have coefficient 2. For example $x_{01}x_{10}x_{12}x_{21}$ comes once from the walk $0,1,2,1,0$ and once from the two walks $0,1,0$ and $1,2,1$. Both contributions have sign $+1$. Exhaustive sign equations over $\mathbb F_2$ already rule out any choice of transition signs. The next argument permits arbitrary complex weights and their limits. [Enumeration and signing equations](data/gct-frontier/clow_moments.py)

## A coefficient equation for arbitrary scalar transitions

Cut a four-edge path after the second edge. Its physical state records the current head and vertex. At that cut allow every two-edge prefix its own scalar weight and every two-edge suffix its own scalar weight. A path's weight is their product. This includes all programs assigning an independent complex multiple of $x_{uv}$ to every allowed transition, including the choice of next head on closing. The constraint that each transition uses its prescribed variable is essential.

Set $j=2$, take $i=1$ or 3, and write $\ell$ for the other vertex. Below, a two-digit pair denotes an arc and adjacent pairs denote multiplication of the corresponding variables. The letters stand for coefficients of the output polynomial.

| | First coefficient | Second coefficient | Unwanted coefficient |
|---|---|---|---|
| 1 | $a=[0\ell,\ell i,i0,jj]$ | $b=[0\ell,\ell0,ii,jj]$ | $k_1=[0i,ii,i0,jj]$ |
| 2 | $c=[0\ell,\ell j,ji,i0]$ | $d=[0\ell,\ell0,ij,ji]$ | $k_2=[0i,ij,ji,i0]$ |
| 3 | $e=[0\ell,\ell i,ij,j0]$ | $f=[0\ell,\ell j,j0,ii]$ | $k_3=[0i,ii,ij,j0]$ |

Each of the first six coefficients is a single prefix times a suffix. Each unwanted coefficient is a sum of two such products. The three cut states are $(0,i)$, $(0,j)$ and the start of the next walk after closing. Write $p_1,p_2,p_3$ for the prefix weights reaching those states from $0\to\ell$ and $u_1,u_2,u_3$ for the corresponding weights from $0\to i$. For nonzero $p$ the common suffixes give

$$
\begin{pmatrix}k_1\\ k_2\\ k_3\end{pmatrix}=
\begin{pmatrix}a&0&b\\0&c&d\\e&f&0\end{pmatrix}
\begin{pmatrix}u_1/p_1\\u_2/p_2\\u_3/p_3\end{pmatrix}.
$$

Define $D_i=adf+bce$ and $N_i=adk_3-dek_1+bek_2$. Cramer's rule gives $N_i/D_i=u_2/p_2$ whenever these quotients exist. Exchanging $i$ and $\ell$ interchanges the two prefixes through $(0,j)$. Hence the polynomial

$$
\Phi=N_1N_3-D_1D_3
$$

vanishes. A direct expansion proves the identity also when weights or denominators are zero. At the permanent $a,b,c,d,e,f$ are all one and $k_1,k_2,k_3$ are zero, so $\Phi=-4$. Polynomial continuity excludes every coefficientwise limit of this scalar family. Lean generates the four-step graph, verifies the contributing paths, computes the coefficients of the project's own permanent, and proves the limit obstruction. [Lean certificate](data/gct-frontier/ClowMoments.lean)

For $m>4$, multiply each tested monomial by the singleton loops at all other vertices. Each spectator must form its own closed walk since it has only a loop available. The two-step prefixes still meet the same suffixes, including any required spectator loops in increasing head order. This proves the obstruction in every size $m\ge4$. The proof also works for any three distinct nonzero labels $i,j,\ell$ with the same role for zero. In particular, a deterministic memory scheme whose value after two steps depends only on the two row origins $0,z$ needs different labels for all $m-1$ choices of $z$. Two choices $i,\ell$ sharing that label restore the scalar factorization on the two sets of nine coefficients. This conclusion allows complex transition weights and applies to that specified type of memory. The spectator and memory arguments are paper proofs.

## What additional memory achieves

Allow vector-valued states, so a transition multiplies $x_{uv}$ by a matrix. One exact construction stores the set of row origins already consumed. Discard a path when it repeats an origin. At degree $m$ the survivors are exactly the permutation covers. For four rows the maximum number of histories at a single physical state after each successive edge is $1,2,1$. After two edges, the next row origin $v$ is known at the state. There are only two possible nonzero origins other than $v$ for the preceding edge. One bit distinguishes them. The third edge checks that its next origin is the other choice. Lean proves that these two local gates compute the full four-row permanent. Together with the sextic this proves the optimal maximum channel dimension for this graph at four rows is **two**, even if scalar limits are allowed. [Lean proof of both bounds](data/gct-frontier/ClowMoments.lean) · [Exact enumeration](data/gct-frontier/clow_moments.py)

There is a sharp lower bound with nonnegative real transition matrices. Fix the physical state $(0,j)$ after $k$ steps. For each $(k-1)$-subset $S$ of vertices outside $\{0,j\}$, take the path from zero through $S$ in increasing order to $j$. Take the suffix from $j$ through the other vertices outside $\{0,j\}$ in increasing order back to zero. Joining a prefix and its matching suffix gives a Hamiltonian cycle and its unique walk. Crossed choices repeat a row and miss another. With nonnegative weights, the contribution of the crossed path is bounded by its entire monomial coefficient. In a sequence tending to the permanent the square matrix of path weights therefore tends to the identity. It factors through the channel at $(0,j)$, which must have dimension at least $\binom{m-2}{k-1}$. Conversely, at any state the visited $k$-set contains zero and omits the next row origin, giving this same upper bound on histories per state. The ten-row peak is **70**. [Lean rank statement for the limiting identity](data/gct-frontier/MomentRank.lean)

There is an all-size family inside the cubic budget. Retain only physical states that occur in some permutation cover. At cut $1\le k<m$, a walk still at head zero can be at any of the other $m-1$ vertices. At heads $1\le h<k$ any current vertex $u\ge h$ is possible. At head $k$ only the new start $(k,k)$ is possible, since all smaller origins have already been used. These choices are attained by taking smaller vertices as singleton cycles and putting the other required vertices in a simple cycle. The count is $km-\binom{k}{2}$, and summing over cuts gives $m(m^2-1)/3$ physical states. **Three coordinates at each state therefore give a size-$m^3-m+1$ pencil**, inside the project’s target for every $m\ge2$. The exact history construction fits three coordinates through $m=5$. At $m=6$ it first needs six. The three-channel sum-of-origins trial at $m=6$ used a size-125 pencil and left coefficient 2 on the witness with repeated row 1 and missing row 4.

At ten rows there are $10,19,27,34,40,45,49,52,54$ physical states at the successive internal layers, totaling 330. Distinguishing all histories would use 4,608 internal states. Giving each physical state up to four coordinates, capped by the number of its histories, uses 984. This second choice has room for genuine matrix weights at size **985**, within the target of 1,001. [State counts and six-row trial](data/gct-frontier/clow_moments.py)

I instantiated that family using the sum modulo four of the row origins already read. Every matching has the correct final residue. The transitions use the interior-loop sign above and retain residues reached by at least one genuine history at the corresponding physical state. This produces 971 internal states and a size-972 pencil. Its middle block is strictly layered, so its only possible nonzero transfer moment is $cT^8b$. All $10!$ permutation coefficients equal one by uniqueness of their walks. On the monomial

$$
x_{01}x_{10}x_{12}x_{21}\prod_{v\notin\{0,1,2,5\}}x_{vv}
$$

the coefficient is **2**. Row 1 is repeated and row 5 is missing. Replacing 5 by 6 as the missing row gives coefficient zero. There are 84 witnesses of this form with $i\equiv\ell\bmod4$, collectively exposing errors on all eleven restrictions from the previous experiment. A full-rank zero-one input gives a short numerical check. Take

$$
X=\begin{pmatrix}1&1&0\\1&1&1\\0&1&1\end{pmatrix}\oplus I_7.
$$

It has permanent **3** and the pencil evaluates to **19**. On the dense integer input $x_{ij}=((7i+11j+3ij+2)\bmod9)-4$, direct evaluation gives $-737{,}920{,}710$ for the pencil and $279{,}786{,}636$ for the permanent. The shared-label obstruction shows that tuning the scalar weights on this residue scheme cannot repair it. [Reproducible ten-row pencil](data/gct-frontier/clow_moments.py)

## A necessary test for any exact corank-one moment solution

This last argument allows arbitrary complex linear forms in the blocks $c,T,b$. Expand them in the input coordinates. For each ordered word $w=(e_1,\dots,e_d)$ of length at least two its coefficient before commutation is $c_{e_1}T_{e_2}\cdots T_{e_{d-1}}b_{e_d}$. The commutative coefficient is the sum over the distinct orderings of its multiset. Assume the degree-$m$ moment is the permanent and all lower moments vanish.

Choose one nonzero ordered word for each perfect matching. At a cut after $k$ letters, record the pair of row and column sets of its prefix. A fixed pair can arise from at most $k!(m-k)!$ different matchings, so at least $\binom{m}{k}$ pairs occur. Retain that many distinct pairs and a representative word of each. Use all cuts $1\le k<m$. Index a matrix $H$ by these choices, in increasing cut order. Its $(a,b)$ entry is the word coefficient obtained by joining prefix $a$ to suffix $b$. This splits as a row times a column through the same $r$ internal states at every cut, giving $\operatorname{rank}H\le r$.

The $2^m-2$ diagonal entries are nonzero. A strictly upper entry at cuts $k<l$ has length $k+m-l<m$. At equal cuts it joins two different pairs, repeating a row or column. Every such word contributes to a commutative coefficient that must vanish. Let $U$ be the strict upper part of $H$. The lower triangular matrix $H-U$ is invertible, hence

$$
\operatorname{rank}U\ \ge\ 2^m-2-r .
$$

At $m=10$, $r=1{,}000$, the required rank is **at least 22**. This condition applies to any exact solution of the moment system. The argument uses individual ordered coefficients in a single realization. Those coefficients can diverge along a general border sequence. The same proof applies to the determinant, since its matching coefficients are all nonzero. The signed closed-walk determinant program uses at most $9\binom{11}{2}=495$ internal states, so that program realizes cancellation rank at least **527**. The counting of cut pairs, the matrix rank inequality and its specialization to 22 are checked in Lean. The selection of words from the moment identity and their matrix factorization are paper arguments. [Lean cut count and rank bound](data/gct-frontier/MomentRank.lean) · [Nisan’s branching-program rank method](https://doi.org/10.1145/103418.103462)

The first undecided case here for three signed coordinates per physical state is $m=6$. It has 70 physical states and a size-211 pencil. The nonnegative lower bound forces any three-channel solution to use cancellation, and the scalar certificate rules out storing a single shared row label. A construction in the three-channel family for infinitely many sizes would refute the $c=3$ statement. Excluding that family would leave other pencils to consider. The general pencil problem and the asymptotic conjecture remain unresolved.

A subsequent argument rules out this edge-labelled graph throughout the cubic budget for every $m\ge70$, allowing arbitrary complex matrices, nonuniform widths and coefficientwise limits. The six-row case with general signed weights remains open. [Supercubic lower bound](clow-prefix-lower-bound.md)

Run the Python file from the repository root. With the pinned toolchain, from the repository's Lean directory run the following.

```sh
lake env lean ../notes/data/gct-frontier/ClowMoments.lean
lake env lean ../notes/data/gct-frontier/MomentRank.lean
```
