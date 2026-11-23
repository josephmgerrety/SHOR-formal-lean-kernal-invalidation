# Exact Fourier-window arithmetic and coherence laws for discrete-logarithm graph states

This development studies three mathematical objects: the good-output arithmetic in the author-hosted 1994 discrete-log construction, Fourier transforms of graph states with workspace vectors, and finite-copy discrimination of graph-state families. The statements use explicit finite sums, integer congruences and complex inner products.

The development consists of 15 primary Lean modules and three supplementary modules. The latter prove the exact common congruence kernel, certify the padded complex Fourier columns and construct the balanced residue workspace. [Source and theorem index](THEOREMS.md) · [Verification](VERIFICATION.md)

## 1. A concrete 1994 good-output counterexample

The arithmetic certificates establish

$$
p=96{,}097,\qquad n=p-1=96{,}096=16\cdot6{,}006,\qquad q=102{,}102=17\cdot6{,}006.
$$

The number p is prime. The element 5 has multiplicative order n in the nonzero residues modulo p, and

$$
5^{22}\equiv78{,}073\pmod{96{,}097}.
$$

The modulus q is obtained by the primorial-division construction:

$$
2\cdot3\cdot5\cdot7\cdot11\cdot13\cdot17=510{,}510,\qquad 510{,}510/5=102{,}102.
$$

The certificates verify that 5 is the largest removable prime that leaves the quotient above p, and that p < q < 2p. These facts connect the fixed arithmetic example to Lemma 3.2 in the author-hosted 1994 paper.

For a first frequency c, write

$$
nc=qc'+z,\qquad 0\le c<q,\quad 0\le c'<n,\quad -q<2z\le q.
$$

The 1994 good-window condition is 20|z| ≤ q. In the certified example,

$$
z=6{,}006(16c-17c'),\qquad |z|\le5{,}105.
$$

Therefore z=0. The complete set of good first-frequency data is

$$
c=17j,\qquad c'=16j,\qquad z=0,\qquad 0\le j<6{,}006.
$$

There are 6006 distinct good coefficients. Exactly 3003 are divisible by 32, so their uniform divisibility proportion is

$$
\frac{3{,}003}{6{,}006}=\frac12>\frac{10}{32}.
$$

Every good coefficient is divisible by 16. Consequently no good coefficient is coprime to 32, although 32 is a prime power greater than 20 dividing n. Both formalized finite-sample unit-existence statements are false.

The probability calculation also retains the second Fourier frequency. For k=22, the complete good pairs are exactly

$$
(c,v)=(17j,\;101{,}728j\bmod 102{,}102),\qquad 0\le j<6{,}006.
$$

For the complex QFT phase root = exp(2 pi i/q), each accepted pair has probability n/q^2 after summing over the output fibers. The total probability of all accepted pairs is 16/289. The probability of accepted pairs whose coefficient is divisible by 32 is 8/289. Thus the conditional probability is exactly

$$
\frac{8/289}{16/289}=\frac12.
$$

This establishes a counterexample to the displayed 10/R divisibility estimate and the associated unit-existence statement at these source-valid parameters. The finite sums are evaluated exactly, with no numerical approximation to the complex phase.

The formalization follows Lemma 3.2 and Section 7, pp. 5 and 8–10, of the author-hosted 1994 paper. [Shor, *Algorithms for quantum computation: Discrete logarithms and factoring*](https://math.mit.edu/~shor/papers/algsfqc-dlf.pdf)

The author identifies this PDF as a version containing minor corrections. [Shor’s electronic publications](https://math.mit.edu/~shor/elecpubs.html)

## 2. The exact common congruence ambiguity

Each complete good pair supplies the rounded integer

$$
e=nJ-kc'
$$

and the congruence

$$
kc'+e=nJ.
$$

All good coefficients are multiples of 16. The supplementary theorem [`ShorArithmeticStrengthening.all_good_congruences_exact_kernel`](ShorArithmeticStrengthening.lean#L14) identifies precisely which key differences preserve every such congruence:

$$
\big(\forall c'\text{ good},\ n\mid \delta c'\big)\quad\Longleftrightarrow\quad 6{,}006\mid\delta.
$$

The coefficient c'=16 itself is good and supplies the converse. Thus the common ambiguity modulo 96096 is the set of 16 shifts

$$
k+6{,}006s\pmod{96{,}096},\qquad 0\le s<16.
$$

A separate certificate proves that the 16 representatives for k=22 are distinct. A coefficient divisible by 32 admits the 32 shifts k+3003s. An individual coefficient can admit additional candidates; c'=0 admits every key. The common-kernel statement concerns the intersection of the constraints from all good coefficients.

At $c'=16$ the congruence fixes $k$ modulo $6{,}006$. The additional public relation $5^k\equiv78{,}073\pmod{96{,}097}$ supplies information independent of the good congruences. The unit-existence result identifies where division in the displayed argument fails.

## 3. Window-collapse theorems and the 1997 modulus

Write n=hN and q=hQ with h>0, N>0, Q>0 and gcd(N,Q)=1. For the q/20 window, Q < 20 forces z=0 and yields exactly

$$
c=Qj,\qquad c'=Nj,\qquad 0\le j<h.
$$

Any factor greater than 1 shared by N and a modulus R prevents every good c' from being a unit modulo R. The restriction to a proper coefficient ideal requires N>1. The analogous q/12 result holds under Q < 12.

The expanded paper uses q equal to a power of two with p < q < 2p. The supplementary certificate [`ShorArithmeticStrengthening.power_two_modulus_for_96097`](ShorArithmeticStrengthening.lean#L39) establishes the corresponding values

$$
q=2^{17}=131{,}072,\qquad\gcd(96{,}096,131{,}072)=32,\qquad Q=4{,}096.
$$

Therefore the Q < 12 collapse theorem does not apply to this prime under the expanded paper's modulus choice. For p=101 and q=128, the reduced modulus is Q=32, also outside that range.

There is a further arithmetic distinction. With power-of-two q, n < q and Q < 12, the reduced modulus Q lies in {2,4,8}, while N is odd and N < Q. Hence N lies in {1,3,5,7}. This elementary deduction is separate from the supplied general window theorem. It shows why the concrete 1994 modulus cannot simply be carried over to the 1997 parameter choice.

The expanded paper gives the revised parameter conditions (6.10)–(6.11) in Section 6. [Shor, *Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer*](https://arxiv.org/abs/quant-ph/9508027)

## 4. Complete good pairs for n=100 and q=128

The original table certificates identify coefficient gcds and exact congruence solution sets. The supplementary theorem [`Shor2AdicQFTBridge.shor_100_complete_table_rows`](Shor2AdicQFTBridge.lean#L102) also verifies the second frequency and phase inequality for each row, using the q/12 window and k=22:

| $c$ | $v$ | $c'$ | $z$ | $J$ | Candidates modulo 100 |
| ---: | ---: | ---: | ---: | ---: | --- |
| 9 | 59 | 7 | 4 | 2 | 22 |
| 18 | 118 | 14 | 8 | 4 | 22, 72 |
| 41 | 123 | 32 | 4 | 8 | 22, 47, 72, 97 |

For w=n(kc+v-Jq)-kz, the three residuals are 12, 24 and 12. Each satisfies 2|w|≤100, and each second frequency is below 128. The second row satisfies the q/12 window and fails the narrower q/20 window. The table therefore records complete 1997-window pairs.

## 5. Exact workspace coherence and Fourier line mass

Let n>0 and let e(a,b) be unit vectors in a complex inner-product space, indexed by a,b in ZMod n. The graph output is t=a-kb. For the normalized n-point Fourier amplitudes A(k,u,v,t), the development proves

$$
1-\sum_{u,t}\lVert A(k,u,-ku,t)\rVert^2=\frac{1}{2n^3}\sum_{t,b,b'}\lVert e(t+kb,b)-e(t+kb',b')\rVert^2.
$$

The right side is nonnegative and vanishes exactly when e is constant on each graph-output fiber. Equivalently, there is a function f such that

$$
e(a,b)=f(a-kb).
$$

Under the unit-vector hypothesis, this fiber condition is equivalent to the ideal joint Fourier law:

$$
P(u,v)=\begin{cases}1/n,&ku+v=0,\\0,&ku+v\ne0.\end{cases}
$$

Vector Parseval and the normalization module establish total probability 1 for this order-n Fourier model.

The original [`Shor2AdicMasterBridge.two_adic_workspace_line_defect_and_survival`](Shor2AdicMasterBridge.lean#L29) theorem substitutes an assumed variance of 2n^3(1-2^(-r)) into the defect identity. The supplementary balanced-label theorem derives the variance from more explicit hypotheses. Let n=dm with d>0. Let a label map assign each b to one of d classes, with exactly m elements in each class. Require squared distance zero for workspace vectors with equal labels and squared distance 2 for those with different labels, within every output fiber. Retain the unit-vector hypothesis.

The supplementary proof counts the pairs and derives

$$
\text{total variance}=2n^3(1-1/d),\qquad\text{line defect}=1-1/d,\qquad\text{line mass}=1/d.
$$

The supplementary module also constructs the labels and vectors explicitly: residueLabel(b)=b.val mod d, and labelWorkspace(a,b) is the corresponding standard basis vector in the complex Euclidean space of dimension d. It proves that every residue class contains exactly m elements, that the vectors have unit norm, and that their squared distances are zero or 2 as required. Consequently [`ShorResidueWorkspace.residue_workspace_variance`](ShorResidueWorkspace.lean#L196) and [`ShorResidueWorkspace.residue_workspace_line_survival`](ShorResidueWorkspace.lean#L207) derive the displayed laws directly from n>0, d>0 and n=dm, without assuming the variance equality. Setting d=2^r gives the concrete theorem [`ShorResidueWorkspace.two_adic_residue_workspace_line_survival`](ShorResidueWorkspace.lean#L216) with survival 2^(-r). This is a specified residue-recording workspace model. A clean workspace e(a,b)=constant satisfies the ideal fiber condition.

## 6. Binary-stage and padded Fourier identities

For n=2^r m, shifting a key by sm leaves the multiplier 2^j k modulo n unchanged at every stage j≥r. This is the theorem [`Shor2AdicTorsionHierarchy.binary_control_stage_invariance`](Shor2AdicTorsionHierarchy.lean#L16). The low stages remain capable of distinguishing the keys. The examples modulo 100 and 116 certify these integer congruences. The module contains no elliptic-curve equation or point-count certificate, so the modulus-116 results have the formal scope of cyclic arithmetic.

For n=d n0 and k=d k0, the canonical fiber representative

$$
a(t,b)=(t+kb)\bmod n
$$

has period n0 in b. Consequently the raw padded Fourier sum factors as

$$
S(u,v,t)=\Phi_d(v)B(u,v,t),\qquad\Phi_d(v)=\sum_{j=0}^{d-1}\omega^{v j n_0}.
$$

Here B is the sum over one period. This factorization is an identity over a commutative ring. For d=2, the filter is 1+root^(v n0), so root^(v n0)=-1 forces the full amplitude to vanish.

The supplementary module certifies the actual complex root exp(2 pi i/128), its 128th power 1 and its 64th power -1. It then proves that the columns v=32 and v=96 have zero amplitude for every u and output fiber t, for each of n=100 and n=116 with k=22. The corresponding normalized Born masses, summed over fibers, are zero.

The sign condition alone does not annihilate every d-term filter. At d=3 the filter is 1-1+1=1, as certified by [`Shor2AdicQFTBridge.odd_torsion_filter_counterexample`](Shor2AdicQFTBridge.lean#L109). Over the complex numbers the general geometric-filter cancellation requires a nontrivial dth root as the step phase.

## 7. Parity and scalar-field distinctions

Multiplying each b term by (-1)^b shifts the second Fourier frequency by q0 when root^q0=-1. Summing a joint function over its second frequency is invariant under that frequency translation. A separate collision-sum theorem removes the parity factors when every colliding pair b,b' has equal parity. The arithmetic collision lemma supplies that parity conclusion for an even reduced order and an odd reduced multiplier. The formal second-marginal result is stated as a collision-weighted finite-sum identity; a fully instantiated padded marginal requires the corresponding Fourier collision expansion.

The unnormalized Hadamard matrix H0 satisfies H0^2=2I over the integers. Its reduction modulo 2 is nonzero and has square zero. Since det(H0)=-2, the inverse H0/2 exists over the rationals and complex numbers, while H0 has no integer matrix inverse. The normalized complex gate H0/sqrt(2) is unitary. The characteristic-two matrix identity concerns a different scalar field.

The Boolean sign character (-1)^(ua) has period two in u. The supplied theorem establishes that periodicity, without asserting a full rank theorem for a separately defined transform.

## 8. Finite-copy zero-error discrimination

For n>1 and a finite copy count t, the normalized graph-state family is

$$
\lvert\Psi_k\rangle=\frac1n\sum_{a,b}\lvert a,b,a-kb\rangle .
$$

The family in the theorem consists of $t$ independent copies of these vectors.

The formal tensor-product coefficients are nonnegative real numbers. Every pair of these states has positive inner product, witnessed by their common all-zero coordinate together with nonnegativity of all other contributions.

The POVM lemmas prove that certainty of correct identification of distinct labels requires orthogonal states. Grouping finitely many measurement outcomes through a fixed classical decoder gives the same conclusion. Therefore no fixed finite-outcome measurement and decoder identifies every k with probability 1 from exactly t copies of this graph-state family.

This is a zero-error state-discrimination theorem. It supplies no bounded-error impossibility result and no lower bound on the computational complexity of discrete logarithms. Its input consists of the stated graph copies. Algorithms using the public classical instance, additional operations or a variable stopping time require their own formal models.

## 9. Formal coverage

The master theorem assembles selected arithmetic, parity and finite-copy propositions. Separate declarations establish the probability ratio, general window families, workspace identities, complete table rows and complex zero columns. All are included as roots of the complete export. [Master theorem](Shor2AdicMasterBridge.lean) · [Complete declaration index](THEOREMS.md)
