# Shor's Algorithm — Lean Kernel Invalidation

**Joseph M. Gerrety 

## Introduction

This development studies three mathematical objects: the good-output arithmetic in the author-hosted 1994 discrete-logarithm construction, Fourier transforms of graph states with workspace vectors, and finite-copy discrimination of graph-state families. The statements use explicit finite sums, integer congruences and complex inner products.

The central question is what a sample classified as **good** actually tells us. The 1994 argument uses good Fourier outputs to obtain a congruence involving an integer coefficient $c'$. To divide by that coefficient modulo a prime power $R$, some good sample must supply a $c'$ coprime to $R$. For the certified prime $p=96{,}097$, every good coefficient is a multiple of 16, while $32$ is a prime power greater than 20 dividing $p-1$. No good sample can supply the required unit modulo 32. The obstruction survives the use of complete pairs of Fourier frequencies and their exact Born weights. [1994 paper, Lemma 3.2 and Section 7, pp. 5 and 8–10](https://math.mit.edu/~shor/papers/algsfqc-dlf.pdf)

## Formally Proven Mathematical Invalidations

### 1. The $10/R$ divisibility estimate fails at $R=32$

Lean certifies that $p=96{,}097$ is prime, $g=5$ has multiplicative order $n=p-1=96{,}096$, and the formalized primorial construction gives $q=102{,}102$, with $p<q<2p$. Set $h=6{,}006$, so $n=16h$ and $q=17h$. The first frequency $c$, its coefficient $c'$, and its centered residual $z$ satisfy $nc=qc'+z$. The good window requires $20|z|\le q$. Therefore

$$
z=6{,}006(16c-17c'),\qquad |z|\le 5{,}105.
$$

Only $z=0$ satisfies both conditions. The complete list of good triples is $(c,c',z)=(17j,16j,0)$ with $0\le j<6{,}006$. Exactly 3,003 of the 6,006 coefficients are divisible by 32. This gives a counting proportion of $1/2$. [`Shor1994Integrated.certified_prime_field_counterexample`](Shor1994Integrated.lean#L7) · [`Shor1994Invalidation.good_first_iff_exact_lattice`](Shor1994Invalidation.lean#L182) · [`Shor1994Invalidation.printed_ten_over_thirty_two_bound_false`](Shor1994Invalidation.lean#L259)

Counting coefficients alone would leave open what weighting by the quantum amplitudes does. For $k=22$, the proof retains the second measured frequency $v$. Each good pair has the unique form $(17j,101{,}728j\bmod 102{,}102)$. At the complex root $\exp(2\pi i/q)$, summing the squared amplitude over the output fibres gives weight $n/q^2$ for each accepted pair. The total good mass is $16/289$ and the divisible good mass is $8/289$. The resulting **conditional probability** is

$$
\Pr\!\left(32\text{ divides }c'\mid (c,v)\text{ is a complete good pair}\right)=\frac{8/289}{16/289}=\frac12>\frac{10}{32}.
$$

The values come from exact finite sums over the graph outputs. Page 9 of the 1994 paper describes the count of good first frequencies as approximately $q/10$. Page 10 uses a lower bound of one tenth to derive the pointwise $10/R$ estimate before equation (7.41). Here the exact proportion of good first frequencies is $6{,}006/102{,}102=1/17$, and the proportion of good coefficients among all $n$ coefficients is $1/16$. This finite witness invalidates the stated pointwise estimate. An asymptotic statement about all sufficiently large primes would require a separate argument. [`Shor1994Invalidation.complete_good_pair_iff_indexed`](Shor1994Invalidation.lean#L587) · [`Shor1994Invalidation.source_raw_total_good_probability`](Shor1994Invalidation.lean#L745) · [`Shor1994Invalidation.source_raw_divisible_good_probability`](Shor1994Invalidation.lean#L794) · [`Shor1994Invalidation.actual_qft_conditional_bound_false`](Shor1994Invalidation.lean#L871)

### 2. Finite samples of good coefficients cannot supply the required unit

The formalized existence claim allows a **different** coefficient for each required large prime power $R$. Even with that freedom, the condition at $R=32$ fails for every good coefficient. The proof takes an arbitrary proposed finite sample, asks for its witness at 32, and applies the divisibility result to that witness. An explicit complete good pair establishes that the good event is nonempty. The two Lean conclusions are the negations of the predicates `PaperUnitExistenceClaim` and `PaperCompletePairUnitClaim`. [`Shor1994Invalidation.paper_unit_existence_claim_false`](Shor1994Invalidation.lean#L295) · [`Shor1994Invalidation.paper_complete_pair_unit_claim_false`](Shor1994Invalidation.lean#L313) · [`Shor1994Invalidation.explicit_complete_good_pair`](Shor1994Invalidation.lean#L322)

### 3. The good rounded congruences retain an exact common ambiguity

The rounded information has the form $kc'+e\equiv0\pmod n$. A shift $\delta$ preserves **every** good coefficient equation exactly when $6{,}006\mid\delta$. Every coefficient is a multiple of 16, and the single good coefficient $c'=16$ gives the converse. Modulo $96{,}096$ this leaves 16 common candidates. It invalidates unique recovery from this collection of congruences alone. Additional information such as the public group relation supplies a separate constraint. [`ShorArithmeticStrengthening.all_good_congruences_exact_kernel`](ShorArithmeticStrengthening.lean#L14) · [`ShorArithmeticStrengthening.sixteen_distinct_common_candidates`](ShorArithmeticStrengthening.lean#L33) · [`Shor2AdicMasterBridge.source_good_pair_sixteen_coset_blindness`](Shor2AdicMasterBridge.lean#L67)

### 4. The ideal Fourier line law has an exact workspace condition

For $n>0$, let $e(a,b)$ be unit workspace vectors in a complex inner-product space. Write $t=a-kb$ and let $A(k,u,v,t)$ denote the normalized order-$n$ Fourier amplitude. The mass missing from the line $v=-ku$ is exactly the sum of the within-fibre squared distances, with the following normalization.

$$
1-\sum_{u,t}\lVert A(k,u,-ku,t)\rVert^2
=\frac{1}{2n^3}\sum_{t,b,b'}\lVert e(t+kb,b)-e(t+kb',b')\rVert^2 .
$$

Consequently the ideal law holds precisely when $e(a,b)$ factors through the graph output $a-kb$. A single pair of unequal vectors on one fibre rules it out. For the explicit workspace that records $b\bmod 2^r$ in orthogonal basis states, $n=2^r m$ and $n>0$ give line mass $2^{-r}$. The proof derives the variance by counting labels. These statements specify the workspace being measured. [`LeanFiberFourier.exact_fourier_line_defect`](LeanFiberFourier.lean#L189) · [`LeanFiberFourier.ideal_pair_law_iff_output_factor`](LeanFiberFourier.lean#L216) · [`LeanFiberFourier.unequal_fiber_vectors_forbid_ideal_law`](LeanFiberFourier.lean#L226) · [`ShorResidueWorkspace.two_adic_residue_workspace_line_survival`](ShorResidueWorkspace.lean#L216)

### 5. Perfect discrimination fails for every fixed finite copy count

Fix $n>1$ and a natural number of copies $t$. The normalized graph vectors for labels $k\in\mathbb Z/n\mathbb Z$ have positive mutual overlap. Every vector has a common nonzero all-zero coordinate, and the terms contributing to the inner product are nonnegative. Perfect discrimination by a positive operator-valued measure (POVM) requires distinct labels to have orthogonal states. Hence there is no single finite-outcome measurement and fixed decoder whose probability of the correct label is 1 **for every label** on those $t$ graph copies. The conclusion concerns exact discrimination from those states. The paper's bounded-error algorithm and its factoring construction are outside that proposition. [`ShorGraphCopies.graphVector_inner_re_pos`](LeanGraphCopies.lean#L69) · [`LeanMeasurementNoGo.perfect_discrimination_implies_orthogonal`](LeanMeasurementNoGo.lean#L49) · [`ShorFiniteCopyNoGo.no_perfect_decoded_measurement_on_graph_copies`](LeanFiniteCopyNoGo.lean#L20) · [`ShorFiniteCopyNoGo.every_group_order_and_finite_copy_count`](LeanFiniteCopyNoGo.lean#L43)

### 6. Modulus choice, padding and scalar field determine which deductions apply

| Question | Checked conclusion and source |
| --- | --- |
| When does the $q/20$ good window force a lattice? | For $n=hN$, $q=hQ$, $h,N,Q>0$, $\gcd(N,Q)=1$ and $Q<20$, the good triples are exactly $(Qj,Nj,0)$ for $0\le j<h$. A factor greater than 1 common to $N$ and $R$ rules out a good unit modulo $R$. [`ShorWindowFamily.good_first_iff_exact_lattice`](ShorWindowFamily.lean#L98) · [`ShorWindowFamily.no_finite_good_sample_supplies_unit`](ShorWindowFamily.lean#L133) |
| Does the same witness meet the 1997 hypotheses? | The expanded paper uses a power-of-two transform size and a $q/12$ window. At the same prime $q=131{,}072$ and $Q=q/\gcd(n,q)=4{,}096$. The sufficient condition $Q<12$ fails for this witness. [`Shor2AdicTorsionHierarchy.good_residue_zero_1997`](Shor2AdicTorsionHierarchy.lean#L159) · [`ShorArithmeticStrengthening.power_two_modulus_for_96097`](ShorArithmeticStrengthening.lean#L39) |
| Which padded Fourier columns vanish? | For $n\in\{100,116\}$, $q=128$ and $k=22$, the half-period filter vanishes at frequencies $v=32,96$. Every amplitude in these columns is zero, as is its mass summed over graph outputs. The length-three signed filter instead sums to $1$. [`Shor2AdicQFTBridge.actual_qft_zero_column_born_mass`](Shor2AdicQFTBridge.lean#L67) · [`Shor2AdicQFTBridge.odd_torsion_filter_counterexample`](Shor2AdicQFTBridge.lean#L109) |
| What does a shared binary control imply? | For $n=2^r m$, $k$ and $k+sm$ yield equal control multipliers at stages $j\ge r$. The proof identifies those stages. Its hypotheses leave lower stages unrestricted. [`Shor2AdicTorsionHierarchy.binary_control_stage_invariance`](Shor2AdicTorsionHierarchy.lean#L16) |
| Over which scalars does the square vanish? | The unnormalized Hadamard matrix squares to $2I$ over the integers. Its reduction modulo 2 squares to zero. The predicates specify their scalar fields. [`Shor2AdicTorsionHierarchy.hadamard_int_sq_eq_two_id`](Shor2AdicTorsionHierarchy.lean#L377) · [`Shor2AdicTorsionHierarchy.hadamard_mod2_sq_eq_zero`](Shor2AdicTorsionHierarchy.lean#L383) |

The 1994 and 1997 parameter conventions are given in the two primary sources. [Author-hosted 1994 version](https://math.mit.edu/~shor/papers/algsfqc-dlf.pdf) · [Expanded paper, Section 6](https://arxiv.org/abs/quant-ph/9508027)

## Independent kernel verification

The formal development contains **18 mathematical modules and 202 public theorems**. The recorded proof export selected **251 public declarations**, including definitions and structures on which the theorems depend. Both independent checkers, **con-leche** and **con-ron**, accepted 21,530 declarations in the exported dependency closure, and Lean’s default kernel accepted the same export. The per-declaration audit observed only `propext`, `Classical.choice` and `Quot.sound` across the complete root list. [Verification record and reproduction commands](VERIFICATION.md) · [Complete declaration index](THEOREMS.md)

## Source and further reading

The root module imports the complete development. The detailed exposition gives the first- and second-frequency derivations, examples, parity laws, normalization and exact hypotheses of the state-discrimination theorem. The line-linked index includes every public declaration with its individual axiom dependencies. [Root module](ShorSuite.lean) · [Mathematical exposition](MATHEMATICS.md) · [Theorems and definitions](THEOREMS.md)
