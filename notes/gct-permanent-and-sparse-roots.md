# Permanent level spaces, sparse products and affine-plane rectangle covers

Research note, 25 November 2026. The symmetric permanent problem L-gct-231 has maximum dimension two over $\mathbb Q$, by an exhaustive calculation over $\mathbb F_5$ and a lattice argument. The complex case remains open in this investigation. L-gct-195 and L-gct-196 ask for dimension bounds of 8 and 9 for rectangular permanent level spaces over $\mathbb C$. L-gct-272 asks for a bound of 22 distinct positive roots over $\mathbb R$, with Lean's empty roots multiset for the zero polynomial. The sections below give the rectangular bounds under a row-support hypothesis and the unconditional root bounds $13\le M\le31$. [Project statements](https://data.pequalnp.com/data/desk/gaps.json)

For the permanent problem, the paper proof below establishes $\dim L\le q+2$ whenever $L$ contains $q-2$ independent perturbations supported in a common row. This reaches the requested bounds at widths six and seven under that hypothesis. [Proof](#four-independent-pure-directions-at-width-six-and-the-general-width-bound)

## A checked project result in finite geometry

**L-meta-10022 and L-meta-10020.** Covering the nonincidences of the affine plane of order five by all-nonincident rectangles requires at least twelve rectangles. The two posted statements ask whether eleven and ten rectangles, respectively, are insufficient. Both encode the point–line incidence matrix by 25 integers. On 25 November 2026 the project's local verifier checked each file against its posted statement. We submitted each proof independently. [Lean proof of the twelve-rectangle lower bound](../lean/PEqualNP/Outside/L_meta_10022.lean) · [L-meta-10022 submission](https://github.com/open-goat/pequalnp-proofs/pull/16255) · [L-meta-10020 submission](https://github.com/open-goat/pequalnp-proofs/pull/16267)

There are 25 points, six incident lines through each, and 30 lines in all, giving $25(30-6)=600$ nonincidences. A rectangle consists of a set $R$ of points and a set $C$ of lines missing every point of $R$. The sharp bound is $|R||C|\le54$. Eleven rectangles therefore cover at most $594$ nonincidences, even before overlaps are counted.

De Winter, Schillewaert and Verstraëte study this maximum product as an invariant of finite incidence geometries. In communication complexity the same product is the size of a monochromatic rectangle. Dividing the number of required entries by the maximum rectangle size connects the two questions directly. [De Winter, Schillewaert and Verstraëte](https://mathweb.ucsd.edu/~jverstra/incidence-free.pdf) · [Fiorini, Kaibel, Pashkovich and Theis, §§4–5](https://arxiv.org/abs/1111.0444)

The formal proof checks two affine permutations against the actual matrix. One fixes point 0 and cycles through the other 24 points. The other sends point 1 to 0. Together they take any ordered pair of distinct points to $0,1$. Rectangles containing fewer than two points have area at most 30. Once $0,1\in R$, only 19 lines are eligible. Lean branches on those lines, maintaining the common set of points they miss. It prunes whenever even keeping every remaining line and every currently available point gives area at most 54. The proof of this search invariant applies to every subset of the remaining lines.

Equality has a geometric explanation. In the project's numbering, row $5x+y$ represents $(x,y)\in\mathbb F_5^2$. The conic $x^2-2y^2=1$ has point indices $5,12,13,17,18,20$. All nine lines with indices $1,4,7,8,10,15,22,23,25$ miss it, producing a rectangle of area $6\cdot9=54$.

### A counting proof of the sharp rectangle bound

The bound of 54 also has a proof without enumeration. Complete the affine plane to its projective plane of 31 points. For a set $S$ of $r$ affine points put $D(S)=\sum_{\ell:\,k_\ell\ge3}\binom{k_\ell-1}{2}$, where $k_\ell=|S\cap\ell|$. Each affine point belongs to six lines and each pair determines one line. Counting the lines disjoint from $S$ therefore gives

$$
d(S)=30-6r+\binom r2-D(S).
$$

Every seven-point set in the projective plane has $D(S)\ge2$. Otherwise there is at most one triple line and every other line meets the set in at most two points. At a point of $S$ off the triple, the other six points fill its six lines, giving no tangent. Each point on the triple has one tangent. Thus the only possible odd-intersection lines are the triple and its three tangents. They contain at most $3+3\cdot5=18$ outside points in total. But for each of the 24 outside points the six lines through it partition $S$, so at least one meets $S$ oddly. This contradiction also rules out a seven-point set with no triple. Projective duality gives the corresponding assertion for lines.

Every eight-point set has $D(S)\ge4$. If $D(S)\le3$ and there is a four-point line, it is the only line with three or more points. Removing a point of that line leaves seven points with a single triple. Otherwise there are at most three triple lines. Each survives five of the eight single-point deletions, giving at most 15 total triples across the resulting seven-point sets. Each of the eight sets needs at least two, giving at least 16.

For $r=1,\ldots,6$ the displayed identity gives respective upper bounds $24,19,15,12,10,9$ for $d(S)$. For $r=7$ it gives at most seven disjoint lines. For $r\ge8$ any eight-point subset gives at most six. With $c\le5$ selected lines their union contains at least $5c-\binom c2$ affine points by the two-term inclusion–exclusion inequality, so $c(25-5c+\binom c2)\le50$ for $0\le c\le5$. With six selected lines the same inequality leaves at most ten points outside. Equality would require six distinct directions and no three concurrent lines. Adding the line at infinity would give seven projective lines with no triple concurrence, which the seven-point argument excludes by duality. So six lines leave at most nine points outside. These cases give $r c\le54$ throughout.

## Rational obstruction for the symmetric permanent problem

**L-gct-231 over the rationals.** The maximum dimension of a rational linear space of symmetric $4\times4$ matrices with $\operatorname{per}(J+T)=24$ is two. The same upper bound holds for a complex linear space defined over $\mathbb Q$. The project's existential statement permits arbitrary complex coefficients. This is a finite-computation proof for the rational case. [Reproduce the enumeration](data/gct-frontier/symmetric_permanent_mod5.py) · [Project desk](https://pequalnp.com/desk/step?gap=L-gct-231)

For the lower bound, put $a,b,-a-b$ in the three off-diagonal positions of the first row and their transposed positions, and put zero elsewhere. Write $v=(1+a,1+b,1-a-b)$. In the permanent of the shifted matrix, permutations fixing the first position contribute 6. Picking its image and preimage in the other three positions gives $2(\sum v_i)^2=18$ for the remaining permutations. The parameters are independent.

For the upper bound, a rational three-plane $W$ would give a saturated rank-three lattice $W\cap\mathbb Z^{10}$ in the ten symmetric entries. Its quotient in $\mathbb Z^{10}$ is torsion-free, so this lattice is a direct summand. A basis stays independent modulo five. The integer polynomial $\operatorname{per}(J+\sum t_i B_i)-24$ vanishes identically over $\mathbb Q$, so its coefficients vanish modulo five as well. In particular there would be a three-plane over $\mathbb F_5$.

The exhaustive computation gives the following counts over $\mathbb F_5$.

| Vector dimension | Spaces on the permanent level |
|---|---:|
| 1 | 3,918 |
| 2 | 156 |
| 3 | 0 |

To reproduce the count, first impose vanishing of the linear coefficient of $\operatorname{per}(J+tT)-24$. This coefficient is six times the sum of all entries, so one diagonal entry is determined. Normalize the first nonzero one of the nine remaining coordinates to one, giving $(5^9-1)/4=488281$ candidates. On this hyperplane the quadratic coefficient is $\sum_{ij}T_{ij}^2-2\sum_i(\sum_jT_{ij})^2$. After it vanishes, evaluations at $t=1,-1$ detect the cubic and quartic coefficients. The script computes both permanents directly from all 24 permutations.

Over $\mathbb F_5$, the projective line through $a,b$ consists of their two projective points and the four points $a+cb$, $c=1,2,3,4$. Test every unordered pair of surviving points, recording each complete line once. A projective plane would contain a complete line and an outside point joined by complete lines to each of its six points. No such pair exists. Extending scalars can introduce further projective points and lines, which is the outstanding issue in applying this computation to the complex statement.

## Literature and the nearest formal results

| Source | Result and relevance |
|---|---|
| Algebraic geometry | Chan and Ilten study planes on the common zero set of the individual permanental minors. Their Grassmannian charts and tangent-space calculations suggest testing an extension of a given plane by differentiating along it. Our four equations require cancellation in **sums** of minors. A compression-space classification for individual minors would require a separate implication. [Chan and Ilten, §§2–3, 7](https://doi.org/10.2140/ant.2015.9.629) |
| Matroid theory | Rado's independent-transversal theorem lets the three-row proof select one independent evaluation functional per column. Prescribing its value kills one entry in each shifted column. The project has generalized the resulting **sum of column products** theorem to any row count. For four rows, passing from the injective-column sum to that expression introduces three products of pairwise contractions. [Rado (1942)](https://doi.org/10.1093/qmath/os-13.1.83) · [Three-row argument](../lean/PEqualNP/Gct/Helpers/ThreeRowRado.lean) · [General column-product theorem](../lean/PEqualNP/Gct/L175.lean) |
| Enumerative combinatorics | Möbius inversion on the partition lattice removes the distinct-column condition. With zero row sums, the quartic is $M_{12}M_{34}+M_{13}M_{24}+M_{14}M_{23}-6M_{1234}$, where $M_I=\sum_j\prod_{i\in I}t_{ij}$. The coefficients come from the partitions of types $2+2$ and $4$. The same inversion gives the cubic cofactor used below. [Rota, *On the Foundations of Combinatorial Theory I*](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/rota1.pdf) |
| Fewnomials and real analysis | Koiran, Portier and Tavenas bound zeros of sums of products by controlling Wronskians. For $A=pq,\ B=rs$, the first relevant numerator is $A'B-AB'$. On intervals avoiding zeros of $B$, Rolle bounds the crossings of $A/B=1$. Their general Theorem 12 gives a much larger estimate at these parameters. A proof of 22 by this route needs a sharper count for this numerator or the intervals where a crossing is possible. [Koiran, Portier and Tavenas, §§2–3](https://arxiv.org/pdf/1205.1015) |
| Oriented matroids and real algebraic geometry | The two equations $py=r,\ sy=q$ retain the factor structure lost in expansion. The circuit theorem of Bihan and Dickenstein applies to support size $n+2$ in $n$ variables. Our bivariate system can have up to sixteen monomials. Bihan's 2026 preprint treats arbitrary supports via Gale duality, coefficient signs and a Rolle recursion. Its bounds concern nondegenerate positive solutions. An application here must treat both signs of $y$, zero denominators, and multiple roots of the elimination polynomial. [Bihan and Dickenstein](https://arxiv.org/abs/1601.05826) · [Bihan, preprint v3](https://arxiv.org/abs/2610.06435v3) |
| Stability theory | The Hermite–Biehler theorem relates Hurwitz stability to interlacing of even and odd parts. Below it gives a construction for **any thirteen prescribed distinct positive roots** in the four-factor class. [Yang and Zhang, Theorem 2.1](https://dmtcs.episciences.org/articles/2510/download) |
| Probability and algebraic complexity | Briquel and Bürgisser bound the expected root count with independent Gaussian coefficients. Worst-case examples can depend on finely chosen coefficients. The project already has a certified example of eight positive roots for two trinomials multiplied together and shifted by one, using tightly spaced evaluation points. Koiran's complexity implication concerns a uniform bound over growing descriptions. [Briquel and Bürgisser](https://arxiv.org/abs/1806.00417) · [Trinomial witness](../lean/PEqualNP/Outside/L_gct_261.lean) · [Koiran](https://arxiv.org/abs/1004.4960) |

The closest checked upper bounds are $6$ for $4\times4$ and $7$ for $4\times5$. The real-field theorem gives $p+q-2$ using the quadratic form. Over $\mathbb C$ the quadratic form on the total-sum-zero tangent space already admits isotropic spaces of dimensions 11 and 13 at the two target widths. The seven-dimensional row-centered example at width six also breaks the proposed shortcut of bounding every row-centered space by $q-1$. [Four columns](../lean/PEqualNP/Outside/L_gct_214.lean) · [Five columns](../lean/PEqualNP/Outside/L_gct_215.lean) · [Real-field bound](../lean/PEqualNP/Gct/L158.lean) · [Row-centered example](../lean/PEqualNP/Outside/L_gct_198.lean)

## A dimension bound for spaces containing the zero-sum directions of one row

**Proposition.** Let $q\ge4$, let $J$ be the all-ones $4\times q$ matrix, and let $L$ be a complex linear space on which $T\mapsto\operatorname{per}(J+T)$ is constant. Here the rectangular permanent sums over injections of rows into columns. If $L$ contains every perturbation supported in one fixed row whose entries sum to zero, then $\dim L\le q+1$. Equality is attained for every $q\ge4$.

**Proof.** Put that row first. Write its perturbation as $a$ and the remaining three rows as $B$. Let $P_j(z)$ be the permanent of the bottom three rows of $J+zB$ with column $j$ deleted. Changing the first row by $e_j-e_k$ gives $P_j(z)=P_k(z)$. Expansion in the first row now gives $(q+z\sum_j a_j)P_j(z)=q(q-1)(q-2)(q-3)$. Both factors are constant. Thus $\sum_j a_j=0$, and projection onto $B$ has kernel of dimension $q-1$. Write $E$ for its image.

For $d=1,2,3$, write $C_d$ for the sum of degree-$d$ products in $B$ using distinct rows and columns, counting each matching once. Use $C_d^{(-j)}$ after deleting column $j$. These are the nonconstant coefficients of $P_j$ up to nonzero completion factors. Consequently $C_d^{(-j)}=0$, and $(q-d)C_d=\sum_j C_d^{(-j)}=0$. The linear equations imply that every column $b_j$ of $B$ sums to zero.

Let $s=\sum_j b_j$. Subtraction of the quadratic equations before and after deletion gives $b_j\cdot b_j=s\cdot b_j$, with the bilinear dot product. Indeed the matchings using column $j$ contribute $\sum_{i\ne k} b_{ij}(s_k-b_{kj})$. Choose a primitive cube root $\omega$ and write

$$
b_j=u_j(1,\omega,\omega^2)+v_j(1,\omega^2,\omega),\qquad U=\sum_j u_j,\quad V=\sum_j v_j.
$$

These are linear forms on $E$. Each basis vector has square length zero, and their mutual product is 3. The quadratic equation becomes

$$
(2u_j-U)(2v_j-V)=UV.
$$

If both totals are nonzero forms, choose $y\in E$ where their product is nonzero. For $k\in\ker U\cap\ker V$, the right side is constant and nonzero on $y+\lambda k$. Each factor on the left must be constant on this line, because a nonconstant affine linear polynomial has a root. Hence all $u_j(k),v_j(k)$ vanish. The map $E\to\mathbb C^2$ given by $(U,V)$ is injective.

If either total is the zero form, the simultaneous kernel $K=\ker U\cap\ker V$ has codimension at most one in $E$. On $K$, $u_jv_j=0$ as an identity of polynomial functions. This ring is an integral domain, so each active column has a fixed orientation. Its entries have the form $(t_j,\eta_j t_j,\eta_j^2t_j)$, where $\eta_j=\omega$ or $\omega^2$. Every row now sums to zero.

For clarity, write the three rows as $x,y,z$ and $M_{xy}=\sum_i x_i y_i$, with analogous notation for the other pairs. Inclusion-exclusion gives the full injective cubic $2\sum_i x_i y_i z_i=0$. Deleting column $j$ changes it to

$$
x_jM_{yz}+y_jM_{xz}+z_jM_{xy}-6x_jy_jz_j=0.
$$

After substitution, orientations that differ contribute $1+\omega+\omega^2=0$, while equal orientations contribute 3. For each active $j$ we get

$$
t_j\left(\sum_{i:\eta_i=\eta_j}t_i^2-2t_j^2\right)=0.
$$

Within one orientation all nonzero coordinate forms have the same square, so each equals a fixed form up to sign. In fact each active orientation has exactly **two** nonzero columns on $K$. If there are $m$ such forms with common square $t^2$, the displayed equation gives $mt^2=2t^2$. Their signs are opposite because their sum is zero. The two representative forms determine every entry of $K$. Thus $\dim K\le2$. This finishes the upper bound when $U=V=0$.

It remains to exclude $\dim K=2$ when precisely one total is nonzero. Exchange orientations if necessary so $U\ne0,\ V=0$. In dimension two the two representative forms on $K$ must be independent. Choose $k\in K$ with all $v_i(k)=0$ and with $u_\alpha(k)=1,\ u_\beta(k)=-1$ on the active $u$-pair. There is also an active $v$-column $j$ outside this pair. The quadratic identity on **all of $E$** forces $2u_j=U$, since $v_j$ is a nonzero form.

In the cube-root basis, the bottom cubic on any set $S$ of columns is
$$
6\bigl(e_3((u_i)_{i\in S})+e_3((v_i)_{i\in S})\bigr).
$$
Here $e_3$ sums over unordered triples of distinct columns. In the permanent of a triple, a mixed choice of orientations contributes zero; three equal orientations contribute 6 times the product of their coordinates. Apply the full cubic and the cubic with $j$ deleted to $x+\lambda k$, for arbitrary $x\in E$. In the full cubic divided by 6, the coefficient of $\lambda^2$ is $-\sum_{i\ne\alpha,\beta}u_i(x)$. In the deleted cubic it is the same sum with the $j$-term removed. Both coefficients vanish. Hence $u_j=0$ on $E$, contradicting $2u_j=U$. In the one-total case $\dim K\le1$ and $\dim E\le2$. This proves the upper bound in all cases. The line argument, its dimension consequence, the signed-generator step and the mixed cubic identity have Lean proofs. The cofactor reduction and dimension argument as a whole are a paper proof. [Lean lemmas](data/gct-frontier/RowForms.lean)

For equality take the top row arbitrary with sum zero, $u=(s,-s,0,0,\ldots)$, $v=(0,0,t,-t,0,\ldots)$. The bottom columns all sum to zero, also after any one column is deleted. The quadratic on a column set $S$ is $-3[(\sum_S u)(\sum_S v)-\sum_S u_i v_i]$. The two supports are disjoint and, after any one deletion, at least one pair still sums to zero. The cubic vanishes because each orientation occupies at most two columns. All first-row cofactors are therefore the same constant, giving a level space with $q-1+2$ free parameters. At width six this is the project's L-gct-198 construction. [Six-column witness](../lean/PEqualNP/Outside/L_gct_198.lean)

**Restriction from five columns.** Keep any five columns and let $S$ be the deleted columns. The kernel of evaluation on $S$ identifies with a five-column level space, since all positive-degree matchings involving a deleted column vanish there. Rank-nullity gives $\dim L\le7+\operatorname{rank}(\mathrm{ev}_S|_L)$. Thus at width six a counterexample must have projection rank at least two on **every** column. At width seven it must have rank at least three on **every** pair. [Five-column theorem](../lean/PEqualNP/Outside/L_gct_215.lean)

## Four independent pure directions at width six, and the general width bound

**Theorem.** Let $q\ge4$ and $L\subseteq\mathbb C^{4\times q}$ be linear. Suppose the rectangular permanent is constant on $J+L$. If $L$ contains $q-2$ linearly independent matrices supported in a common row, then $\dim L\le q+2$. In particular, a nine-dimensional counterexample to L-gct-195 would have at most three pure directions in each row. At width seven, a ten-dimensional counterexample to L-gct-196 would have at most four.

### Cofactors and three split quadrics

Move the distinguished row to the top and choose a $(q-2)$-plane $A$ of pure perturbations there. All its vectors have sum zero, by expanding the permanent in that row. Its annihilator is $\langle\mathbf1,d\rangle$ for a nonzero $d\in\mathbb C^q$ with $\sum_j d_j=0$. The projection of $L$ onto the top row has rank at most $q-1$. Otherwise some perturbation would have top row $-\mathbf1$, making the permanent zero although $\operatorname{per}(J)=q(q-1)(q-2)(q-3)$. Write $K$ for the kernel of this projection, identified with its three lower rows. It suffices to prove $\dim K\le3$.

Use the matching sums $C_e,C_e^{(-j)}$ defined above, now on $K$. For any $B\in K$ the vector of lower permanents with one column deleted annihilates $A$, by varying the top row freely in $A$. Its sum is constant as $B$ varies. Taking homogeneous components, for $1\le e\le3$ the vector of deleted sums lies in $\langle d\rangle$, and $(q-e)C_e=\sum_j C_e^{(-j)}=0$. The coefficient in the expansion of each lower permanent is a nonzero completion factor times the matching sum.

Put $h=(1,\omega,\omega^2)$ and $\bar h=(1,\omega^2,\omega)$ for a primitive cube root $\omega$. Write the lower columns as $b_j=d_jT\mathbf1+u_jh+v_j\bar h$. The linear cofactor equations justify the common linear form $T$, since deleting a column subtracts its sum and $C_1=0$. Write $U=\sum u_j,\ V=\sum v_j,\ f_j=2u_j-U,\ g_j=2v_j-V$. With $s=\sum b_j$, deletion changes $C_2$ by $s\cdot b_j+(\sum_i b_{ij})^2-b_j\cdot b_j$. This equals $3(Uv_j+Vu_j)+6d_j^2T^2-6u_jv_j$. Consequently, for a quadratic form $H$ on $K$,

$$
 f_jg_j=Q(d_j),\qquad Q(z)=UV+zH+4z^2T^2.
$$

The finite sample set $P=\{0,d_1,\ldots,d_q\}$ has at least three distinct members. Indeed, a nonzero centered vector cannot take its values in $\{0,c\}$ for one $c\ne0$. Every sampled value of $Q$ is a product of linear forms, including $Q(0)=UV$.

Suppose first that $Q$ is not identically zero. Let $r\le2$ count its distinct zero values in $P$. Choose three distinct sample parameters including these $r$ values. Lagrange interpolation of the leading coefficient gives

$$
 4T^2=\sum_{i=1}^{3-r}c_i a_i b_i
$$

with nonzero constants $c_i$, where $a_i b_i$ are the nonzero sampled quadrics in this triple. The joint span $S$ of $T$ and these factors has dimension at most $3-r$. Indeed the map given by these linear forms has totally isotropic image for the nondegenerate form $\sum c_i x_i y_i-4t^2$ in $2(3-r)+1$ variables. Its image dimension equals $\dim S$. Interpolation gives $Q(z)\in\operatorname{Sym}^2 S$ at every parameter. Every linear factor of a nonzero such quadric also belongs to $S$. For example, choose coordinates extending a basis of $S$ and use additivity of polynomial degree in each extra coordinate.

Let $D$ be the common kernel of $S$ in $K$. Then $\dim K=\dim S+\dim D$. Call a column exceptional if $Q(d_j)=0$ as a polynomial on $K$. On $D$, the form $T$ vanishes, and $f_j=g_j=0$ at every nonexceptional column. At an exceptional column $f_jg_j=0$ already on $K$, so at least one of its two factors is the zero form. Also $UV=0$ on $D$. If neither factor vanishes as a form on $K$, both belong to $S$ and vanish on $D$.

### Two cubic consequences

**Centered columns of one orientation.** Consider a subspace $E$ on which $T=U=V=0$ and $f_jg_j=0$ for all $j$. Fix an orientation $h$ or $\bar h$ for each column, and write its coordinate as $x_j$ in that orientation. Each orientation has coordinate sum zero. Write $M_\sigma=e_2(x_i:i\text{ in orientation }\sigma)=-\tfrac12\sum_{i\in\sigma}x_i^2$. The full cubic is $6\sum_\sigma e_3(x_i:i\in\sigma)=0$. Subtraction of a deleted cubic from the full one gives, for one cubic $F$ on $E$,

$$
 x_j(x_j^2+M_\sigma)=d_j F.\tag{1}
$$

The sign and factor 6 are absorbed in $F$. If $F=0$, each nonzero coordinate in a fixed orientation has the same square. The moment equation forces exactly two active columns in each active orientation, with opposite coordinates. Thus $\dim E\le2$. At equality there are two disjoint pairs, and their two parameters vary independently.

In fact $\dim E\le2$ also when $F\ne0$. If both orientations have coordinate rank at most one, their coordinates already determine $E$. Otherwise take independent coordinate forms $x,y$ in one orientation, with weights $a,b$. Both weights cannot vanish, since that would give $x^2=y^2$. Elimination in (1) gives

$$
 (b x-a y)M_\sigma=a y^3-b x^3 .
$$

The nonzero denominator puts $M_\sigma,F$ in the rational function field $\mathbb C(x,y)$. Every coordinate in this orientation satisfies the monic cubic in (1), so lies in $\langle x,y\rangle$. An additional independent linear form would be transcendental over $\mathbb C(x,y)$. If the other orientation has a column with nonzero weight, its coordinate divides the nonzero polynomial $F$. Here $F$ belongs to $\mathbb C[x,y]$, since it is a polynomial on $E$ lying in $\mathbb C(x,y)$. That coordinate therefore belongs to $\langle x,y\rangle$, and (1) puts the other moment in $\mathbb C(x,y)$. The monic cubic again accounts for every remaining coordinate.

If the other orientation has only zero weights and has a nonzero coordinate, it occupies exactly two columns with opposite coordinates, as in the $F=0$ argument. Its $e_3$ vanishes, so $e_3$ in the first orientation vanishes too. At width six the first orientation has at most four columns. Pad with zeros to four entries. Substitution of the fourth entry as $-a-b-c$ gives $e_3=-(a+b)(a+c)(b+c)$, so the entries are $x,-x,y,-y$ after reordering. Independent $x,y$ give the two nonproportional cofactor polynomials $-xy^2,-yx^2$, contrary to (1).

For arbitrary width the same case follows from the second moment. If two independent coordinates $x,y$ in the first orientation have nonzero weights $a,b$, evaluate (1) at a point with $x=a,y=b$. This gives $a^2=b^2$. Change the sign of $y$ and its weight if necessary so both weights equal $a$. Subtracting gives $M_\sigma=-(x^2+xy+y^2)$ and $aF=-xy(x+y)$. A nonzero coordinate of weight zero would have square $-M_\sigma$, which has rank two. Each nonzero coordinate thus divides $F$ and is a multiple of one of $x,y,-x-y$. The multiplier is $1$ or $-1$. Indeed, on the line in the $(x,y)$-plane where a different factor of $F$ vanishes, the chosen factor is generically nonzero with square $-M_\sigma$, and (1) gives the multiplier's square as one. Comparing coefficients in $-2M_\sigma=\sum x_i^2$ now gives multiplicity one for each of the three factors. Their product is nonzero, contradicting $e_3=0$. If all nonzero-weight coordinates are multiples of a single $x$, rank two requires an independent zero-weight coordinate $y$, giving $M_\sigma=-y^2$. Comparing the coefficients of $x^3$ and $xy^2$ in (1) shows that every nonzero-weight coordinate is $\pm x$. Every active zero-weight coordinate is $\pm y$. The positive multiplicity of $x^2$ in $\sum x_i^2=2y^2$ is impossible. Finally, if the other orientation is identically zero, the bound for the first orientation already suffices.

**Variation along an opposite pair.** Suppose $k\in K$ has lower columns $h,-h$ at $p,q$ and zeros elsewhere. In the full cubic at $B+\lambda k$, the coefficient of $\lambda^2$ is $-6(U-u_p-u_q)(B)$. Two copies of $h$ contribute only with a third $h$. The coefficient with a third $\mathbf1$ or $\bar h$ vanishes by $1+\omega+\omega^2=0$. Thus $U=u_p+u_q$ on all of $K$. The corresponding coefficient of the deleted cubic is zero for $j=p,q$ and $6u_j(B)$ otherwise. Since the deleted-cubic vector is proportional to $d$, there is a linear form $l$ on $K$ such that

$$
 d_p l=d_q l=0,\qquad u_j=d_j l\quad(j\notin\{p,q\}).\tag{2}
$$

The same conclusion holds for $v,V$ with the opposite orientation.

### Exhausting the zero values of the quadratic family

*If $Q\equiv0$*, then $T=0$ and $UV=0$ as polynomial identities. The common kernel of $U,V$ in $K$ has codimension at most one and satisfies the centered cubic bound above. Thus $\dim K\le3$.

*If $r=0$*, all $f_j,g_j$ vanish on $D$. The identities $\sum f_j=(2-q)U,\ \sum g_j=(2-q)V$ recover both totals and therefore every coordinate. Hence $D=0$ and $\dim K\le3$.

*If $r=2$*, it suffices to show $\dim D\le2$. When $Q(0)\ne0$, both totals vanish on $D$, so the centered cubic bound applies. When $Q(0)=0$, exchange orientations to arrange $V=0$ on $K$. Some nonexceptional column $j_0$ has $d_{j_0}\ne0$, since otherwise every weight would lie in $\{0,c\}$. On $D_0=D\cap\ker U$ this column is zero, so (1) gives $F=0$. If $\dim D\ge3$, the centered bound forces $\dim D_0=2$, with independent opposite pairs of both orientations. Apply (2) for the $u$-pair. Both $j_0$ and a member $j$ of the $v$-pair have $u=U/2$ on $D$. For $j_0$ this follows from $f_{j_0}|_D=0$. For $j$, the factor $g_j$ is nonzero on $D_0$, so $f_j=0$ on $K$. Their weights differ because $j$ is exceptional and $j_0$ is not. Equation (2) now forces $l|_D=0$, hence $U|_D=0$, a contradiction.

*If $r=1$ with nonzero root $\alpha$*, then $Q(0)\ne0$ and both totals vanish on $D$. Centering of $d$ gives a nonexceptional column of nonzero weight. Its coordinate vanishes on $D$, hence $F=0$ in (1). If $\dim D\ge2$, there are two independent opposite pairs, all at weight $\alpha$. For the $u$-pair, (2) gives $l=0$ on $K$, so $u$ vanishes outside this pair. At a member of the $v$-pair the factor $g_j$ is nonzero on $D$, hence $f_j=0$ on $K$. There $u_j=0$, giving $U=0$ on $K$, contrary to $Q(0)\ne0$. Thus $\dim D\le1$ and $\dim K\le3$.

*If $r=1$ with root zero*, arrange $V=0$ on $K$. On $D$ every nonzero-weight column has $u_j=U/2,\ v_j=0$. At least two such columns have different weights because $\sum d_j=0$. Their lower columns are identical on $D$, so their deleted cubics are equal. Proportionality to $d$ forces every deleted cubic to vanish on $D$.

If $U|_D\ne0$, delete a nonzero-weight column and subtract from the full cubic on $D$. One obtains $(U/2)(e_2(u)-U^2/4)=0$. For every column where $v_j=0$, the same subtraction gives $u_j(u_j-U/2)^2=0$. For every column where $v_j$ is nonzero as a form on $D$, the quadratic equation gives $u_j=U/2$ directly. Thus each $u_j$ is either zero or $U/2$. Exactly two can equal $U/2$, by summing, and the two nonzero-weight columns already occupy them. All $v_j$ vanish, so $\dim D\le1$.

It remains that $U|_D=0$. The centered bound with $F=0$ gives $\dim D\le2$. At equality four zero-weight columns form two independent opposite pairs. Apply (2) to both pairs on $K$, with linear forms $l_u,l_v$. At a member of the $v$-pair, $u_j=0$ by (2) and $f_j=0$ by exceptionality, hence $U=0$ on $K$. At every nonzero weight $d_j$, (2) now gives $Q(d_j)=4d_j^2 l_u l_v$. Comparing this with $d_j H+4d_j^2T^2$ at two distinct nonzero weights gives $H=0$. Thus $Q(z)=4z^2T^2$, so $\dim S\le1$. Even in this equality case $\dim K\le1+2=3$, completing the theorem.

**Formal verification.** The Lean module starts with the rectangular permanent and proves that every pure row direction annihilates the cofactor vector. It also proves the three-sample interpolation identity, the dimension bound for a sum of products equal to a square, the dimension bound when the sampled products are all nonzero and span the column products, the two-coordinate bound with both orientations present, and the cubic identities for a doubled orientation and four centered columns. The passage to the quadratic family and the assembly of the exceptional cases are on paper. [Lean lemmas](data/gct-frontier/CofactorConic.lean)

### The next case at width six

With three independent top-row directions, choose centered $d,e$ such that their span with $\mathbf1$ is the annihilator of the chosen three-plane. The same cofactor calculation gives points $p_j=(d_j,e_j)$, linear forms $T_1,T_2$, and quadrics $H_1,H_2$ with

$$
 f_jg_j=UV+d_jH_1+e_jH_2+4(d_jT_1+e_jT_2)^2 .
$$

For every affine dependence $\sum\lambda_j=0,\ \sum\lambda_jp_j=0$, it follows that $\sum\lambda_j f_jg_j=4\sum\lambda_j(d_jT_1+e_jT_2)^2$. One may include the origin as a sample with product $UV$. A dependence on four points can produce a rank-two form on the right. A single such identity gives only a five-dimensional isotropic bound for its four pairs of factors and two extra coordinates. To recover the needed kernel bound of three from this approach, one must use compatibility between distinct dependencies or additional cubic equations.

## Exact extension test for the cube-root example

The first row ranges over all zero-sum vectors. In the bottom three rows the first two columns are $s(1,\omega,\omega^2)$ and its negative, and the next pair is $t(1,\omega^2,\omega)$ and its negative. All remaining lower entries vanish. This defines a space $W$ of dimension $q+1$. The following computation proves that it is inclusion-maximal for both widths. Other level spaces can have larger dimension.

| Width | Dimension of $W$ | Rank of sampled gradients modulo 13 | Quadratic coefficient of normalized candidate modulo 13 |
|---|---:|---:|---:|
| 6 | 7 | 16 | 2 |
| 7 | 8 | 19 | 8 |

First evaluate $\operatorname{per}(J+w)$ exactly in $\mathbb Z[\omega]$ at all nonnegative parameter tuples of total degree at most four. This determines every polynomial of total degree at most four, by triangular interpolation in the binomial basis. All values equal $\operatorname{per}(J)$. An extension direction must annihilate every gradient at these points, in particular those on the degree-three grid. Reduce the gradient equations by $\omega\mapsto3\bmod13$. Subtracting a member of $W$ sets its $q+1$ free entries to zero. Adding these equations and specifying the bottom-right entry gives full rank modulo 13. A square subsystem therefore has determinant invertible in the localization of $\mathbb Z[\omega]$ at this prime.

If the bottom-right entry is zero the direction vanishes after this subtraction. Otherwise normalize it to one. Cramer's rule implies the residue of any complex solution is the unique modular solution of that square subsystem. Its quadratic matching coefficient has the nonzero residue in the table. An extension would have that coefficient zero. The Python certificate recomputes every entry and elimination using integer arithmetic. [Reproduce the certificate](data/gct-frontier/permanent_extension.py)

## Bounds and constructions for the sparse-polynomial problem

Let $M$ be the greatest number of distinct positive roots attained by $pq-rs$ with at most four terms per factor, using the desk's convention at zero. The checked bounds from this investigation are $13\le M\le31$. If the union of the supports of the two products has at most 23 elements, the desired bound of 22 follows already. The Lean proof applies Descartes to the expanded difference and handles cancellation, repeated roots and the zero polynomial. [Lean proofs](data/gct-frontier/SparseRoots.lean)

**Why thirteen roots are natural.** Start with *any* thirteen distinct positive numbers $a_i$. The polynomial $\prod_i(x+a_i)=E(x^2)+xO(x^2)$ is Hurwitz stable. Hermite–Biehler gives real nonpositive roots for both sextics $E,O$. Split each into two real cubics, then replace $x$ by $-x$. The result has the prescribed roots and the form $pq-rs$, with at most four terms per factor. Independently, the Lean witness uses

$$
2^{25}\prod_{a=1}^6(x^2+2^{8a-4})-x\prod_{a=1}^6(x^2+2^{8a}).
$$

Grouping triples gives four tetranomials. Lean verifies opposite signs at successive $4^k$, for $0\le k\le13$, giving thirteen disjoint root intervals. The witness has degree thirteen. [Hermite–Biehler, Theorem 2.1](https://dmtcs.episciences.org/articles/2510/download) · [Formal witness](data/gct-frontier/SparseRoots.lean)

**Why counting coefficient signs alone stops at 31.** Set $p=1+x^2+x^4+x^6$, $q=1+x^8+x^{16}+x^{24}$, $r=x(2+x^2+x^4+x^6)$, and $s=3+x^8+x^{16}+x^{24}$. The even coefficients of $pq-rs$ through degree 30 are positive and the odd coefficients through degree 31 are negative. A uniform improvement must use information beyond that sign sequence. The Wronskian and bivariate approaches retain the two product structures. A decisive counterexample would require 23 distinct positive roots.

## Reproducing the proofs

From the repository root, run the two exact computations with Python 3. Both use only the standard library.

```sh
python notes/data/gct-frontier/symmetric_permanent_mod5.py
python notes/data/gct-frontier/permanent_extension.py
```

With the repository's pinned Lean 4.36.0 and Mathlib cache installed, run the three research modules from the Lean project directory.

```sh
cd lean
lake env lean ../notes/data/gct-frontier/RowForms.lean
lake env lean ../notes/data/gct-frontier/CofactorConic.lean
lake env lean ../notes/data/gct-frontier/SparseRoots.lean
```
