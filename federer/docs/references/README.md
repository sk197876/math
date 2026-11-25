# Source consultation guide

[Documentation](../toc.md) · [Item map](../contents.md) · [Index](../index.md) · [Symbols](../symbols.md) · [Divergences](../divergences.md) · [Bibliography](../bibliography.md)

## Contents

- [Editions and corrections](#editions-and-corrections)
- [Annotation validation](#annotation-validation)
- [Consulted passages: Chapter 2](#consulted-passages-chapter-2)
- [Consulted passages: Chapter 3](#consulted-passages-chapter-3)
- [Consulted passages: Chapter 4](#consulted-passages-chapter-4)
- [English writing](#english-writing)

## Editions and corrections

### Federer’s erratum

Use [federer-erratum.tex](federer-erratum.tex) as the working copy of Federer's
*Geometric Measure Theory: List of corrections*, May 1987. It transcribes the
cover and all twelve numbered correction pages of the user's local scan. The
tables retain the **printed book page and line**; the section headings retain
the **erratum page**. Long replacements for book pages 479 and 499 are set
outside the tables. The bibliographical identity is
[Federer1987Erratum](../bibliography.md#federer1987erratum). The repository's
[original erratum scan](Federer--Geometric-measure-theory--ERRATUM.pdf) is
retained for resolving transcription questions. Transcription conventions are stated in the LaTeX file.
The file contains Federer's corrections, not the project's additional
counterexamples to the book.

An error in the erratum is recorded separately: on erratum p. 3, book
p. 163 line 11 (2.9.18(1)), the printed replacement changes nonempty
intersection to empty intersection in the weighted supremum formula.
The original scan confirms that wording. Taken literally it assigns the
empty set positive value when the first coefficient is one, so it cannot
be a measure. [`weighted_miss_capacity_not_measure`](../../theories/ErratumWeightedHitCounterexample.v#L53) in
[`ErratumWeightedHitCounterexample.v`](../../theories/ErratumWeightedHitCounterexample.v) proves the contradiction. The
formalisation retains the book's nonempty-intersection formula. This is
a **local correction to the erratum**, not a transcription change;
`federer-erratum.tex` preserves the printed wording.

### Project error catalogue

[federer-errors.tex](federer-errors.tex) lists the statements of the book
that the formalisation refutes and that Federer's list does not correct,
together with proposed corrections, the error in the list itself, and the
corrections of the list adopted here. Each entry was checked against the
printed text of the 1969 edition (Springer reprint, which does not
incorporate the 1987 corrections). The catalogue covers the registered
formalisation through 3.4.12 and its completed supplements, together with
the validated items 4.1.1–4.1.24, with explicit omissions and proof limits
retained. Its 142 entries include the local
corrections in 1.4.4–1.4.5, 2.10.11, 3.2.45, 4.1.15 and 4.1.19; the Chapter 3 analytic
corrections; and the convention-dependent line endpoints of 3.2.42–3.2.44.

An editorial note also distinguishes the raw Steiner power from the
normalized quotient in the erratum's p. 5, book p. 275 line 2 replacement.
The scan prints `r^(n-j)`; division by the original `alpha(n-m) r^(n-m)`
leaves `r^(m-j)`. This note does not claim an additional kernel-checked
counterexample. The erratum transcription preserves the scan.
The compiled PDFs are not tracked.

Five entries record further published Chapter 3 corrections: two
bibliographical references, the comparison at book p. 280 line 6, and
the replacements at p. 326 line 3 and p. 327 line 24. The consulted
reprint already prints the corrected p. 280 inequality. These additions
distinguish source records from formal verification of partial or pending
items; they introduce no new claim of mathematical completion.

### Compiling the reference files

Compile the reference without building Rocq or writing generated files here:

```sh
mkdir -p /tmp/federer-erratum-build
pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory=/tmp/federer-erratum-build docs/references/federer-erratum.tex
pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory=/tmp/federer-erratum-build docs/references/federer-errors.tex
```

### Supporting sources and citation conventions

The [bibliography](../bibliography.md) identifies all source editions. The
following notes record which passages were consulted and how they are used:

- [Federer1969](../bibliography.md#federer1969): numbered items such as 1.4.4
  refer to the book; page numbers always mean printed pages.
- [Kelley2017](../bibliography.md#kelley2017): Federer 2.1.6 cites the Appendix.
  Definition 87 and Theorem 88, p. 263, give well-ordering conventions;
  Definition 148 and Theorems 154, 158–159, pp. 275–276, give cardinal
  representatives and comparisons. Historical consistency and continuum-
  hypothesis remarks are not adopted as axioms.
- [Bell2016](../bibliography.md#bell2016): section 1, p. 1, treats Gauss digits;
  section 2, p. 2, gives convergent identities; Theorem 2, p. 5, and the
  cylinder-length formula on p. 6 support the continued-fraction comparison
  in Federer 2.2.9. The unsigned positive error bound printed on p. 2 is not
  used: the preceding identity has alternating sign. Our contraction and
  rational-denominator arguments are proved directly. This source issue is
  separate from Federer's erratum. Federer's [PO, p. 103](../bibliography.md#perron1948) refers to
  [Perron1948](../bibliography.md#perron1948); that passage was not consulted.
- [Saks1934](../bibliography.md#saks1934): Lemma B and its proof, pp. 258–259,
  provide finite rectangular groups with positive common cores and
  small-integral, large-average functions. The actual page scans were
  consulted. This supports the proof of Federer 2.8.20, p. 152.
- [Cesari1939](../bibliography.md#cesari1939): Lemma III, p. 306, expands the
  finite-group construction and harmonic parameter choice; section II.4,
  p. 307, sums the nonnegative constructions at dyadic scales. The actual
  printed pp. 306–307 were consulted. The formal proof uses associated
  measures and the already proved Federer 2.8.7 to select disjoint group
  unions; it does not reproduce the repeated finite packing or invoke a
  differentiation theorem. Federer's original [C2](../bibliography.md#caratheodory1927) citation is
  [Caratheodory1927](../bibliography.md#caratheodory1927), pp. 689–692;
  that passage was not available for direct consultation.

### Source comments

Each named declaration has a `Source for [name]` comment with a Federer
locator and a verbal description of the mathematical source passage. The
comment distinguishes a formalisation of the passage from a supporting lemma,
a construction, a regression example, or a correction. Supporting lemmas need
not be independently stated in the book. Anonymous Hierarchy Builder instances
package the named definitions and proved laws next to them. Export and
assumption-audit files introduce no additional mathematical claims.

Where the source statements use real scalars, the formal statements retain
their explicit field and characteristic hypotheses. Federer 1.6.6 instead
compares complex spaces with their underlying real spaces; its complex scalar
laws have a sealed existence witness. The square-zero exterior universal
property and the ungraded tensor-algebra property are identified as stronger
formulations where applicable.

## Annotation validation

The annotation pass adds source comments to all 2,790 named declarations
(including 2,051 named claims) in the 312 existing `.v` files. Removing only
the newly inserted comments recovers the original source bytes. No definitions,
statements, proof scripts, imports, or compiler directives were changed.
The LaTeX transcription compiles with `pdflatex`. At the time of this
annotation-only pass, Rocq builds, kernel checking and assumption audits were
stopped at the user's request; the comment changes did not constitute fresh
mathematical validation. Subsequent resumed builds and proof audits are
recorded in `docs/verification.txt`.

The counts above describe the original annotation pass. Later proof
changes and their validation have separate records.

## Consulted passages: Chapter 2

### 2.2.12 — Closed approximation and measurability of Suslin sets

Read the complete corollary and proof on book p. 186, the cited
coordinate-pruning and compact-fibre argument in 2.2.12, pp. 68–69, and the
compact-intersection inequality of 2.10.20, p. 182. The working erratum has no
correction to this corollary. The formal proof uses continuity below from
2.10.22 for cutoff measures. It derives the needed open-envelope comparison
directly from cost continuity; it does not claim the stronger interior-cost
infimum equality follows for nonmonotone continuous costs. No identical
compact-approximation corollary was located. The half-error geometric budget
is the same proved strengthening already recorded for the project's 2.2.12.

### Federer 2.10.1: metric open covers

Federer's erratum p. 3, book p. 170 lines 24 and 35, changes the two
references in 2.10.1 from [F11](../bibliography.md#federer1954abstract) to [F12](../bibliography.md#federer1955). The corrected source is
[Federer1955](../bibliography.md#federer1955), Theorem 2.5 on printed
pp. 291–292 and Remark 2.8 on p. 293.
The metric open-cover characterisation is formalised in
[`MetricRefinementCharacterization.v`](../../theories/MetricRefinementCharacterization.v).

The arbitrary-topological extension needs a separate local correction
if the book's open covers of A are read literally. The checked
[`printed_topological_refinement_not_measure`](../../theories/OpenRefinementNonmonotonicity.v#L90) gives a two-point
counterexample to monotonicity. The corrected construction quantifies
over open covers of the whole space, proves the stated measure and
continuous-map conclusions, and agrees with the original formula on
metric spaces. This is a project correction; it is not an additional
entry in, or an alteration to, `federer-erratum.tex`.

### Federer 2.10.20: supporting continuity and open-envelope passages

The four target assertions are on book pp. 181–182. That lemma leaves its
proof as an exercise; the project already proves and seals the envelope used
here. Do not attribute the four identical radial/compact assertions to these
passages. No erratum entry concerns book pp. 181–182.

### Federer 2.10.21: metric profiles and compact convex hulls

The target spans book pp. 182–184. Apply erratum p. 3, book p. 184 lines 8 and
10, to the scope of the final convex density assertion: its ambient sets are
nonempty compact convex sets. The project uses its own proved dimension
reduction and compact parameter images, directly in the supplied norm
topology.

### Federer 2.10.22: compact-cost continuity below

The complete target and proof occupy book pp. 184–186. Its cost is finite,
nonnegative and Hausdorff-continuous, with strict positivity only required on
positive diameters. Positive singleton costs remain permitted. No correction
to this item occurs in the working erratum. The proof uses 2.10.20 radial
exhaustion and 2.10.21 Hausdorff compactness. [Kelley2017](../bibliography.md#kelley2017)'s cited diagonal process
is printed p. 238, Problem D(a), in the local Dover 2017 reprint of *General
Topology* (1955). The formal proof uses instead a compact-product cluster
point and finite-coordinate neighbourhoods at arbitrarily late rows. No
identical compact-cost continuity theorem was located there. Cost ordering,
inactive cover positions and finite-prefix residual bounds are project proof
expansions, recorded separately from Federer's statement and from his erratum.

### 2.10.24 — Weighted covers and upper integrals

For the weighted-cover item 2.10.24, pp. 186–188, both numbered criteria and
the general inequality are checked. The local counterexample
[`closed_ball_hausdorff_closedness_counterexample`](../../theories/ClosedBallHausdorffApproximation.v#L129)
refutes the p. 188 auxiliary closed-ball-family remark in a compact real
subspace. It is separate from the erratum's script-S correction (erratum p. 4,
book p. 188 line 21), and does not disprove the spherical integral equality.
The Hausdorff and spherical specialisations are proved in every
nonnegative real degree, including boundedly compact spaces without a
supplied finite-mass support cover. The original integer interfaces remain.
[`spherical_weighted_proper_equality`](../../theories/SphericalProperWeighted.v#L59)
repairs the false closed-family justification by the existing Hausdorff
comparison. The Gross and integral-geometric applications in the final
paragraph of p. 188 are proved for arbitrary nonnegative extended inputs;
the real-degree Hausdorff and spherical extensions are also complete;
see the [2.10.24 supplement](../checkpoints/2.10.24-supplement-validation.json).

The supporting weighted projection-cover estimates for 2.10.24, p. 188, read
the actual gauge definitions 2.10.4(1) and 2.10.5(1), pp. 172–173, and the
norm formulas and seminorm assertion 2.4.12, pp. 86–87. The estimates are
intermediate results supporting the two final weighted-integral applications
proved in the formalisation.

The Borel-indicator step toward the final paragraph of 2.10.24, p. 188, uses
the full Borel partition supremum of 2.10.8, p. 175, and the metric criterion
2.3.2(9), p. 75. The restricted weighted measure and its abstract supremum
specification are local supporting infrastructure, not additional claims
attributed to those sources.

The complete Gross and integral-geometric applications in the final paragraph
of 2.10.24, p. 188, use the exact Borel-partition supremum of 2.10.8, p.
175, the finite sandwich of 2.2.3, p. 61, and the assigned lower-step
integrals of 2.4.1–2.4.2, pp. 80–81. Borel closed levels of fine covering sums
and their infimum give measurable majorants without assuming the original
input measurable. Finite lower-step fibres transfer to the sealed restricted
weighted measure using null preservation and the finite sandwich, rather than
an implication between arbitrary completed sigma algebras. The working erratum's p.
4 / book p. 188 line 21 entry changes only script S; the closed-ball
counterexample remains a separate local correction. Real-degree
Hausdorff/spherical extensions remain outside the current integer-degree
applications.

### 2.10.25 — Upper-integral estimate for Hausdorff fibre masses

For 2.10.25, pp. 188–189, the actual fibre estimate and proof were read in
Federer. No matching substantive correction appears in the working erratum;
the book p. 188 line 21 entry on erratum p. 4 changes only script S in
2.10.24. Infinite intermediate grouped weights are a local proof
clarification, not Federer's correction.

### 2.10.26 — Fibre measurability and the inclusion counterexample

For 2.10.26, pp. 189–190, the actual statement and the p. 190 scan were read.
The strict V_j cover budget is t+1/j; text extraction omitted that slack.
There is no corresponding erratum entry for pp. 189–190. Federer 2.2.3–2.2.4,
pp. 61–62, supply compact approximation and the nonmeasurable-set existence
argument. they are not attributed the identical fibre theorem or inclusion
example. The historical questions and topological-dimension discussion remain
source context.

### 2.10.27 — Product and spherical section inequalities

For 2.10.27, pp. 190–191, both scanned pages were read. The projection
identity on p. 191 prints an open base ball for a closed source ball; the
formalisation proves the closed-ball identity and an explicit boundary
counterexample. This local correction has no matching entry in the working
erratum. Source-indexed cost sums retain repeated sections instead of relying
on injectivity of the printed family H(y). The zero-dimensional extension is a
project convention, not a claim of that example.

### 2.10.28 — Special interval families and Cantor distributions

For 2.10.28, pp. 191–193, all three Federer scans were read. That condition is
Federer's own correction, erratum p. 4, book p. 192 line 4. The p. 193 line 7
sum index is also corrected there.

### 2.10.29 — Cantor products

For 2.10.29, pp. 193–195, the p. 194 scan was read directly.
The working erratum p. 4, book p. 194 line 8, corrects the last interleaving
term to sigma_j>=t_(j+1)->0. The present explicit-coefficient interfaces do
not assume Euler-Gamma normalisation.

The 2.10.29 product proof includes both local cases on Federer p. 194,
the direct covering-infimum infinity argument, and the finite square covers
on p. 193. The Euclidean plane uses the existing block and scalar
coordinate interfaces. The positive finite-power paragraph on p. 195, including its actual
orthogonal coordinate identification, is proved for explicit
normalising coefficients. Analytic Gamma normalization is proved
in [2.10.2](../chapter2/2.10.md); its positive coefficient may instantiate
these parameterized results. Explicit adapters to the new Hausdorff
interface are not added to the 2.10.29 development.

The positive finite-power proof for 2.10.29, p. 195, uses finite
coordinate-box covers with conserved weights, and products of vanishing local
densities. The latter expands the printed reference to 2.10.27. The final
coordinate permutation is specified by inverse, squared-distance and
membership laws; its recursive witness stays private.

### 2.10.30 — Steiner symmetrisation

For Federer 2.10.30, printed p. 195, the actual passage and the working
erratum were checked. The formalisation retains Federer's compact-source
volume statement and separately proves compactness, convexity and the
boundary-sphere exclusion.

### 2.10.31 — Closed Steiner-stable families contain a centred ball

For Federer 2.10.31, printed pp. 195–196, both actual page scans were checked.
The p. 196 inference following the reflected-cap formula really prints B(a,s),
s<r. The formalisation records a local correction to centre zero and a
concrete singleton obstruction to the printed-centre inference. The May 1987
erratum p. 4, book p. 195 line 20, only changes punctuation and has no entry
for p. 196. its subsequent coordinate-iteration isodiametric argument is not
cited as a proof of 2.10.31.

### 2.10.32 — Lebesgue measure bounded by exterior products

For Federer 2.10.32, printed pp. 196–197, the actual page scans and the
working erratum were checked. Erratum p. 4, book p. 197 line 4, corrects the
raw endpoint bound to mu*alpha(m)^(-1)*2^m (the proof works in R^m); the final coefficient in the
theorem is unchanged. The planar unit-ball regression gives exterior supremum
at least four and diameter at most two. This supporting-source wording
correction is separate from Federer's erratum. The exterior norm passages were
verified separately. They supply algebraic background, not the measure
theorem.

### 2.10.33 — Isodiametric inequality

For Federer 2.10.33, printed p. 197, the actual book scan was read. The project follows
Federer's short deduction from 2.10.32 and 1.7.5. The two independently
verified editions' exterior norm references are those recorded for 2.10.32
above. The working erratum has no additional correction to this corollary.

### 2.10.34 — Gross measure bounded by exterior-diameter measure

For Federer 2.10.34, printed p. 197, use the actual displayed projection chain
and the compact-cover alternative of 2.10.3, p. 172. These are algebraic
supporting references and do not state the Gross comparison. No additional
working-erratum correction applies to this corollary.

### 2.10.35 — Equality of the Euclidean measures

For Federer 2.10.35, printed p. 197, the actual scan and working erratum were
checked. the project retains Federer's density argument for the upper
spherical bound. The other four measure equalities use the actual
full-dimensional projection volume and beta_t(n,n)=1. No additional
working-erratum correction is needed for this item.

### 2.10.36 — Convex endpoint products and the factorial volume bound

For Federer 2.10.36, the actual printed p. 198 was checked, including the
normal projection, exterior-factor comparison, Steiner hull inclusion and
height-times-base volume bound. The scalar calculation behind the last
comparison also uses the actual simplex passage of 2.7.16, p. 136. No
correction for p. 198 occurs in the working erratum. The compact reduction and
use of the sufficient norm inequality are recorded as proof-route expansions,
separately from source corrections.

### 2.10.37 — Exterior-diameter versus convex integral-geometric measure

For Federer 2.10.37, the actual printed p. 198 and the projection-norm
identity of 2.7.16(6), p. 140, were checked. The degree-one coefficient uses
alpha(1)=2 as printed in 2.7.16(1), p. 135. No relevant working- erratum
correction applies. The intermediate Suslin premise ensures measurable norm
inputs on the original open convex generator family; it adds no target
hypothesis to the corollary.

### 2.10.38 — Compact enclosing boxes and attained prefix products

For Federer 2.10.38, the actual printed pp. 198–199 and the box inequalities
in 2.7.16, p. 136, were read. The working erratum has no entry for pp.
198–199. The missing nonempty-source qualification is a local correction, with
an explicit empty-compact counterexample. The intrinsic finite-prefix
implementation follows the same maximal projected-chord induction as the
book's successive coordinate projections; its implementation is hidden and all
downstream geometric properties are derived from the abstract laws.

### 2.10.39 — Spherical measure bounded by exterior measure

For Federer 2.10.39 the printed proof on p. 199 and the degree convention of
2.10.3, pp. 171–172, were read. The latter does not restrict m to n;
above-ambient degrees are included by the dimension-drop argument in 2.10.2,
p. 171, and ambient-degree equality in 2.10.35, p. 197. The working erratum
has no entry for p. 199. Positive enlargements and finite-product continuity
fill in the degenerate-box case left implicit by the book's positive-width
preliminary argument; they are an expanded proof, not an attributed erratum
correction.

### 2.10.40 — Weighted minimum balls and the contact convex hull

For Federer 2.10.40 the actual printed pp. 199–200 were read. No relevant
working-erratum entry applies to pp. 199–200. The formal contact limit uses
nested closed reciprocal constraints in compact P instead of a convergent
subsequence. An explicit uniform-slack proof supplies contact nonemptiness
even when there are no unit directions in ambient dimension zero.

### 2.10.41 — Jung's theorem

For Federer 2.10.41 the actual printed proof on p. 200 was read. The formal
finite support proof reuses local coefficient elimination after translating
one generator to zero; at most n+1 points suffice, without padding or an
affine-independence assertion. No relevant working-erratum entry applies to p.
200.

### 2.10.42 — Jung's spherical/Hausdorff comparison

For Federer 2.10.42 the actual statement on printed p. 201 was read. The
formal interfaces currently use natural degrees. Independent cutoffs t and
t/(q+1) keep the Jung ball diameter strictly within the spherical cutoff
before final suprema. No working-erratum entry applies to book p. 201.

### 2.10.43 — Kirszbraun's theorem

For Federer 2.10.43 the actual printed proof on p. 201 was read. The formal
proof allows nonnegative coefficients and repeated contact points: a strictly
positive weighted squared-distance source budget replaces pruning and the
split between one and several contacts. it has no extension-theorem
counterpart. No working erratum entry applies to p. 201. Both private graph
and scaling witnesses are hidden by opaque
[KirszbraunExtensionSealed.v](../../theories/KirszbraunExtensionSealed.v);
downstream results use only agreement and global-bound laws.

### 2.10.44 — A norm counterexample and scalar Lipschitz extensions

For Federer 2.10.44 the actual printed p. 202 was read. No working-erratum
entry applies to book p. 202. The distance-two sentence is locally qualified
to distinct points; the finite infimum formula needs a nonempty source on an
inhabited ambient space. Both qualifications have proved counterexamples and
are separate from Federer's published corrections. The older 2.5.9
scalar-construction header is corrected only in its comments to cite the
formula's later printed appearance in 2.10.44.

### 2.10.45 — Hausdorff products with a Euclidean factor

For Federer 2.10.45 the actual printed pp. 202–203 were read. No relevant
entry occurs in the working erratum. The local repair for diameter-zero
generators uses positive mesh limits, not positive-diameter enlargements in an
arbitrary metric factor. Natural degrees are covered. The real-degree
product theorem remains unproved here; its actual Gamma normalization
is available from [2.10.2](../chapter2/2.10.md).

### 2.10.46 — Product projection estimates (partial)

For partial Federer 2.10.46 the actual printed pp. 203–204 and the
extended-arithmetic convention in 2.1.1, p. 51, were read.
[Freilich1965](../bibliography.md#freilich1965), Federer's [FR2](../bibliography.md#freilich1965), is the
strict-example source; those examples are not yet formalised.
The introduction, p. 384, attributes the positive Favard result to Freilich's
1950 paper, reference [2] (Federer's [FR1](../bibliography.md#freilich1950)); the 1965 paper does not itself
prove the general I_1 identity quoted by Federer. This citation trail must be
checked against the 1950 proof and the two authors' normalisations. The I_1
assertion remains pending. The 1965 definition uses open convex generators, as
does the project's public Caratheodory projection measure.
[`ProjectionClosedOpenComparison.v`](../../theories/ProjectionClosedOpenComparison.v)
already proves its equivalent closed-convex covering specification, used in
the product upper bound.

The companion [Freilich1950](../bibliography.md#freilich1950), Federer's
[FR1](../bibliography.md#freilich1950), Theorem 4.5, pp. 240–250, proves
the finite analytic cylinder identity through projected-fibre counts,
Haar averaging, and calibration on a unit rectangle. Lemmas 4.1–4.4,
pp. 238–240, discard exceptional rotations. Theorems 5.3 and 5.5,
pp. 257–259, extend to a full-dimensional factor and countably
measurable factors. These passages are source inputs, not completed
Rocq results. Definition 2.1, p. 232, totalises zero times infinity
as zero; this must not be silently transferred to Federer's domain.

## Consulted passages: Chapter 3

### 3.1.1 — Differentials and elementary calculus (pp. 209–211)

For Federer 3.1.1, the actual passage on printed pp. 209–211 was read.
The differential requires an interior domain point and a continuous linear
approximation. The real-source and gradient cases are on p. 209, as is
the local inverse rule (1); the chain and linear rules (2)–(3) are on
p. 210. The gradient paragraph refers back to the polarity and complete
inner-product representation developed in Chapter 1. The erratum, p. 4,
book p. 210 line 26, reverses the difference in the inverse-function
iteration: u_(n+1)-u_n = g(u_(n-1))-g(u_n). This correction is applied in the completed inverse-function proof; it
does not change the opening differential or local inverse statements.

### 3.1.24 — Analytic maps

For Federer 3.1.24 the actual printed pp. 237–241 were read. The
retained erratum has no correction to the first display on p. 241;
the analytic constant two supplies the local constant-term correction
proved in [`AnalyticConstantTermCorrection.v`](../../theories/AnalyticConstantTermCorrection.v). The four conditions,
composition, scalar quadratic inverse, root-set argument and coordinate
expansion follow these passages with the recorded proof constants and
domain conventions. The analytic chart remark on p. 240 is expanded into
proved constant-rank and five-way submanifold equivalence theorems.

The closing nearest-point retraction discussion on pp. 240–241 cites
[Federer1959](../bibliography.md#federer1959), §4. Its bibliographical
information was checked against the retained paper's front matter. That
later positive-reach theorem is a forward reference, not an imported or
assumed proof of an analytic retraction in the present development.

### 3.2.1 — Ordinary and approximate Jacobians (p. 241)

For Federer 3.2.1 the actual printed p. 241 was read. It defines the
ordinary and approximate k-dimensional Jacobians by exterior operator
norms and introduces a roadmap to subsequent area/coarea theorems. The
latter are not assumed in the Jacobian interface. No retained erratum
entry applies to p. 241. The next item must apply erratum p. 4, book
p. 242 line 23, correcting the direction of the orthogonal map in the
polar factorization to O(n,m).

### 3.2.40 — Minkowski-content counterexamples (p. 276)

For 3.2.40, printed p. 276, the local published sources
[Gross1918](../bibliography.md#gross1918), pp. 184–187, and
[Kneser1955](../bibliography.md#kneser1955), Satz 5, pp. 386–387,
were consulted. The Cantor-square proof is registered and validated.
The user deferred the second example; it is not a
completed formalisation. Neither source supplies an assumed theorem or
new project axiom in the registered development.

### 3.3.1 — Cones and projection kernels

For [3.3.1](../chapter3/3.3.md#331--cones-and-projection-kernels),
printed p. 287 was read directly. The displayed cone and projection-distance
formulas and the continuous open probability-preserving kernel map are all
included. The prior invariant-probability statement is 2.7.16(6), p. 139.
No published erratum entry changes 3.3.1. For the next item, 3.3.2,
the published replacements on erratum pp. 5–6, book p. 288 lines 1–6,
require two countable indices and the strict threshold margin; the
uncorrected single-intersection formula is not to be used.

### 3.3.2 — Borel cone-density upper limit

For [3.3.2](../chapter3/3.3.md#332--borel-cone-density-upper-limit),
the literal statement on printed p. 287 and proof on pp. 287–288 were
read with the published replacements on erratum pp. 5–6, book p. 288
lines 1–6. The strict threshold margin and both countable indices are
retained. The proof uses the earlier 2.1.3(4), p. 55, and the rational-ray
criterion of 2.3.2(2), p. 73. No additional source is assumed.

### 3.3.3 — Suslin punctured-fibre accumulation locus

For [3.3.3](../chapter3/3.3.md#333--suslin-punctured-fibre-accumulation-locus),
the statement and proof on printed p. 288 were read directly. The original
punctured affine fibre, positive reciprocal near-point conditions,
projection of S_i and countable intersection are retained. The background
continuous Suslin-image and countable-intersection results are 2.2.10,
pp. 65–66. No published erratum entry changes this lemma.

### 3.3.4 — Almost-everywhere cone-growth trichotomy

For [3.3.4](../chapter3/3.3.md#334--almost-everywhere-cone-growth-trichotomy),
the statement and proof on printed pp. 288–292 were read directly. The
original finite-coordinate inclusions, enlarged aperture equation, active
orthogonal subgroup, actual projective sphere, arbitrary radial numerator
measures and original image fibres are retained. The density step uses
3.2.19, p. 256, and 2.9.17, p. 162; the actual compact-group and invariant
probability results are 2.7.11, pp. 128–130, and 2.7.16(6), p. 139. The
published erratum has no correction to this lemma. The earlier corrected
3.3.2 strict-superlevel formula is used for the original B_j/C_j Borelness.

### 3.3.5 — Cone avoidance and Lipschitz projection sections

For [3.3.5](../chapter3/3.3.md#335--cone-avoidance-and-lipschitz-projection-sections),
the statement and proof on printed p. 292 were read directly. The actual
orthogonal complement, inverse bounds, transverse Kirszbraun extension
from 2.10.43 and sharp orthogonal sum of squares are retained. The countable
small cover uses 2.2.8, p. 64. No published erratum changes this lemma.

### 3.3.6 — Local mass bound for purely unrectifiable sources

For [3.3.6](../chapter3/3.3.md#336--local-mass-bound-for-purely-unrectifiable-sources),
the statement and proof on printed pp. 293–294 were read directly. The
original B, C, height supremum, projected disjoint balls, two-cone inclusion
and exact 12, 7 and 84 factors are retained. The weighted selection is
2.8.4–2.8.5, pp. 143–144; the null remainder uses 3.3.5, p. 292, and
pure unrectifiability from 3.2.14, p. 252. No published erratum changes
this lemma. Infinite cutoff is retained for the following corollary.

### 3.3.7 — Projection mass comparison

For [3.3.7](../chapter3/3.3.md#337--projection-mass-comparison),
the statement and proof are on printed p. 294. The original restricted
pushforward and its Borel regularisation are retained. Actual projected-ball
estimates use 3.3.6, pp. 293–294; strict measure comparison and exceptional-set
decomposition use 2.9.4–2.9.7 and 2.9.15. Local witnesses discharge all
finiteness and Radon premises. No published erratum changes this item.

### 3.3.8 — Vanishing cone growth on a purely unrectifiable source

For [3.3.8](../chapter3/3.3.md#338--vanishing-cone-growth-on-a-purely-unrectifiable-source),
the statement and proof are on printed p. 295. The proof retains the
original B_i, small pieces E and closed increasing C_j. The fixed-cost
openness is from 3.3.2, pp. 287–288; the mass comparison is 3.3.7,
p. 294; the continuity theorem is 2.1.3(4), p. 55. No published erratum
changes this item.

### 3.3.9 — Infinite cone growth and projected nullity

For [3.3.9](../chapter3/3.3.md#339--infinite-cone-growth-and-projected-nullity),
the statement and original cone inclusion are on printed p. 295; the actual
closed-ball quotient upper limit and 2.9.5 conclusion are on p. 296. The
proof retains the original A, B and projection and distinguishes upper
infinite growth from an ordinary infinite limit. No published erratum
changes this item.

### 3.3.10 — Product and almost-every-projection structure assertions

For [3.3.10](../chapter3/3.3.md#3310--product-and-almost-every-projection-structure-assertions),
all incidence definitions, both product identities, three fixed-projection
assertions and final Fubini conclusion are on printed p. 296. The expanded
measurability proof retains the original closed-measurable outer measure;
no Borel regularity or finite whole mass is added. No published correction
changes this item.

The source account of [3.3.11](../chapter3/3.3.md#3311--forward-example-and-historical-open-question)
refers to printed p. 297. The example is a forward reference to 3.3.19;
the positive-S3 question records the author's historical lack of an
example and is not assumed to have a negative answer.

### 3.3.12 — Rectifiable decomposition with projected-null remainder

For [3.3.12](../chapter3/3.3.md#3312--rectifiable-decomposition-with-projected-null-remainder),
the original two projection hypotheses, decomposition and three-piece
projected-nullity argument are all on printed p. 297. The formalisation
retains the original E, every null subset, all original fibres and the
printed order through 3.2.14 and 3.3.10. No published correction changes
this theorem.

### 3.3.13 — Hausdorff and integral-geometric structure

For [3.3.13](../chapter3/3.3.md#3313--hausdorff-and-integral-geometric-structure),
the original statement, Borel-regularity reduction and 2.10.11 counting
bound are on printed p. 297. The literal mass identity and conclusion
of the equality criterion are on p. 298. All original sets and all
printed exponents remain. No published correction changes this item.

### 3.3.14 — Finite infinity-exponent integral-geometric mass

For [3.3.14](../chapter3/3.3.md#3314--finite-infinity-exponent-integral-geometric-mass),
the full theorem, original counting bound, countable common projection
exception, Radon open approximation and 3.3.12 conclusion are on printed
p. 298. The expanded formal proof uses local finite open-base unions
instead of the printed fine partition cells and the already proved
finite Borel open-infimum theorem. No source correction or extra numbered
hypothesis is added.

### 3.3.15 — Positive upper density and original pure remainder

For [3.3.15](../chapter3/3.3.md#3315--positive-upper-density-and-original-pure-remainder),
the theorem and complete regularisation/density-stratum/3.3.12/countable
assembly argument are on printed p. 299. Actual 2.10.19(3), p. 181,
and 2.10.11 give the printed projection hypotheses. The Borel upper-density
assertion is expanded using actual enlarged closed balls and a countable
strict-margin cutoff formula. No source correction is required. Source
identifiers and publication information are in [the bibliography](../bibliography.md).

### 3.3.16 — Other geometric measures and exponent agreement

For [3.3.16](../chapter3/3.3.md#3316--other-geometric-measures-and-exponent-agreement),
the four replacement assertions and finite-infinity exponent agreement
are on printed pp. 299–300. The modified proof uses actual 2.10.6,
2.10.8, 2.10.10, 3.3.12, 3.3.14 and 3.2.26. The following finite-t
question, compact counterexample reformulation and bibliographical
reference remain historical source accounts, not assumed theorems.
No source correction is required. See [the bibliography](../bibliography.md).

### 3.3.17 — Small-cone-density rectifiability criterion

For [3.3.17](../chapter3/3.3.md#3317--small-cone-density-rectifiability-criterion),
printed pp. 300–301 supply the exact small-cone criterion with its aperture
power, actual countable rational tests and density-one argument. The
proof discharges the cited 3.2.14, 3.3.6, 2.8.18 and 2.9.11 hypotheses.
The exact upper-density equality includes infinity. No source correction
is needed. See [the bibliography](../bibliography.md).

### 3.3.18 — Densities and tangents of measure-rectifiable sets

For [3.3.18](../chapter3/3.3.md#3318--densities-and-tangents-of-measure-rectifiable-sets),
printed p. 301 supplies both density/tangent assertions and the false
converse of 3.3.17. The formalisation discharges the actual 2.10.19,
3.2.19 and 3.2.16 appeals and supplies an actual finite positive atomic
counterexample with countable topological support. Bracketed X arguments
retain the original strict cone, as its explicit identity in 3.3.4 confirms.
No correction or degree-zero exclusion is needed. See
[the bibliography](../bibliography.md).

### 3.3.19 — Nested circular-disc planar example

For [3.3.19](../chapter3/3.3.md#3319--nested-circular-disc-planar-example),
printed pp. 302–306 supply the original disc construction and exact measure
and density assertions. The p. 304 positive integral-geometric quantities
are convex Q, not ordinary all-Borel I. The formalisation proves a local
auxiliary strict-radius counterexample at p. 305 and repairs the inclusion
using local buffers, preserving the numbered density conclusion. This
correction is absent from the published working erratum and is recorded in
[the project error list](federer-errors.tex). Published p. 307 corrections
concern the next example, 3.3.20. Sources use [the bibliography](../bibliography.md).

### 3.3.20 — Fixed-binary Cantor square

For [3.3.20](../chapter3/3.3.md#3320--fixed-binary-cantor-square), use
both published p. 307 corrections in [the working erratum](federer-erratum.tex).
The actual original singleton counterexample qualifies the auxiliary
finite-stage attainment assertion on p. 308; it leaves the numbered
Hausdorff and Gross values unchanged. This local qualification is recorded
in [the project error list](federer-errors.tex). All sources are identified
in [the bibliography](../bibliography.md).

### 3.3.22 — Historical density and rectifiability discussion

[Subsection 3.3](../chapter3/3.3.md) is complete. Its closing historical
density discussion, 3.3.22 on printed pp. 309–310, is recorded in a
[source account](../checkpoints/3.3.22-source-account.md), following
Federer's explicit statement that those results are neither proved nor
used. The forward reference to 4.2.25 remains a Chapter 4 task. No new
correction was needed in 3.3.21 or this historical account.

### 3.4.1 — Critical values and the dimension problem (p. 310)

The [3.4.1 account](../chapter3/3.4.md#341--critical-values-and-the-dimension-problem-p-310)
records the opening critical-value problem on printed p. 310. Its definitions
and supporting rank results are validated; the announced upper theorem
and sharpness are proved in 3.4.3–4. No correction to the book was needed.

### 3.4.2 — Four estimates on manifold families (pp. 310–316)

The [3.4.2 account](../chapter3/3.4.md#342--four-estimates-on-manifold-families-pp-310316)
follows the four assertions (6)–(9) on printed pp. 310–316: the
oscillation implication, simultaneous compact flat decomposition,
two-scale real-degree image estimate, and full tangent-critical image
estimate. The statements retain arbitrary normed targets and the
original source sets. No erratum entry applies to these pages; no local
correction or additional theorem hypothesis was needed. The
[divergence map](../divergences.md) records equivalent coordinates and
expanded covering and finite-mass arguments.

### 3.4.3 — Critical-value upper theorem (pp. 316–317)

The [3.4.3 account](../chapter3/3.4.md#343--critical-value-upper-theorem-pp-316317)
follows the theorem on printed pp. 316–317 and its Hahn–Banach,
orthogonal-kernel, and inverse-function reduction to 3.4.2(9). The
complete original upper theorem is validated for arbitrary normed
targets. Rank-stratum and countable-cover details expand the printed
local-to-global argument. No erratum entry, local source correction,
or extra numbered-theorem hypothesis applies. Sharpness is proved in 3.4.4.

### 3.4.4 — Sharpness examples (pp. 317–318)

The [3.4.4 account](../chapter3/3.4.md#344--sharpness-examples-pp-317318)
follows the original binary Cantor correspondence, flat Whitney extension,
and exact-rank product map on pp. 317–318. Actual product probabilities
supply positive real-dimensional Hausdorff image mass and prove the
least-degree assertion. The erratum p. 6 correction to book p. 318 line 26
adds a bibliographical reference; it changes no mathematical assertion.
The closing references to external arc examples are source accounts.

### 3.4.5 — Analytic germs and local algebra (pp. 318–321)

The [3.4.5 account](../chapter3/3.4.md#345--analytic-germs-and-local-algebra-pp-318321)
follows the analytic germs, metric, growth classes, ideals and conditional
Noetherian consequences on pp. 318–321. It records the nonempty-germ
convention required for proper primes and unique component families.
[Cartan1957](../bibliography.md#cartan1957), pp. 97–99, supplies the cited
local/global examples. The formalisation adapts the cubic surface to a
one-sided flat coefficient and proves its obstruction by real Taylor
coefficients. The published coefficient and complex proof are distinguished
from that adaptation. The compact-component result cited to 3.4.8(11)
is now validated in [`AnalyticSetCompactComponents.v`](../../theories/AnalyticSetCompactComponents.v).

### Weierstrass division and preparation, 3.4.6 (pp. 321–324)

Read the original regularity conditions on p. 321, both numbered
assertions on p. 322, the mixed series and absolute majorant on
pp. 322–323, and the weighted quotient recursion and preparation
argument on p. 324 in [Federer1969](../bibliography.md#federer1969).
No published correction changes this item. The
[3.4.6 account](../chapter3/3.4.md#346--weierstrass-preparation-pp-321324)
records the proved original statements, retained actual derivatives,
opaque interfaces and explicit proof adaptations. All registered checks
passed; see the [validation record](../checkpoints/3.4.6-validation.json).
At the start of 3.4.8, apply the published correction at
book p. 326 line 3 to its dual basis space.

### Real analytic reduction, 3.4.7 (pp. 324–325)

Read the two null exceptional-direction sets on p. 324, then the
Noetherian and unique-factorization inductions on p. 325 in
[Federer1969](../bibliography.md#federer1969). The formalisation expands
the printed finite-module and Gauss references within the project.
Actual division and its unique finite remainders prove that distinguished
polynomial primes remain analytic primes. This proves the final
paragraph's nontrivial factor reflection by a different route; it does
not identify the selected factors with preparations of the two given
analytic factors. See the [3.4.7 account](../chapter3/3.4.md#item-3-4-7).
No published correction changes this item. All registered item checks
passed; see the [validation record](../checkpoints/3.4.7-validation.json).

### 3.4.8 — Analytic stratification (pp. 326–337)

Registered validation covers definitions (1)–(4) and every numbered
conclusion (5)–(16). The stronger auxiliary proof claim remains outside
that certification. Apply
both published corrections: p. 326 line 3 places the second basis in
the covector space; p. 327 line 24 replaces the complete boundary and
earlier-stratum assertions. See the [item account](../chapter3/3.4.md#item-3-4-8).

The expanded algebra uses these primary passages:

- [Bourbaki1972](../bibliography.md#bourbaki1972), Chapter III, §2, no. 10,
  Corollaries 1 and 3, p. 184: polynomial and finite-algebra Noetherianity.
- The same book, Chapter III, §3, no. 1, Corollary 1, p. 197:
  Artin–Rees; §3, no. 2, Proposition 5, pp. 200–201: Krull intersection.
- The same book, Chapter V, §1, no. 1, Theorem 1, pp. 303–304:
  the finite-module criterion for integrality.
- [Bourbaki1990](../bibliography.md#bourbaki1990), Chapter IV, §2, nos. 1–2,
  pp. IV.14–18: polynomial division and factorization over a field.
- The same book, Chapter V, §3, no. 1, Theorem 1 and Corollary 1,
  pp. V.16–17; §3, no. 2, Proposition 2, p. V.18; §4, no. 2,
  Proposition 4, pp. V.21–22: algebraic extensions and separability.
- The same book, Chapter V, §7, no. 2, Proposition 3, pp. V.37–38,
  and §7, no. 4, Theorem 1 and Proposition 7, pp. V.40–41:
  the separable primitive element theorem.

These are proof sources. The corresponding algebraic arguments are
proved within the project. The stronger sigma-compactness sentence for
$E_m$ on p. 328 is not certified; the numbered Borel conclusion is
proved by actual compact incidence projections and finite Borel
operations. This distinction is retained in the divergence register.

### 3.4.9 — Analytic families (p. 337)

The component-family theorem uses the original local analytic-set
definition of 3.4.5, p. 321, and every corrected law of 3.4.8(11),
p. 327. The sphere-cut argument retains the original functional equations
and inequality. Compact closed balls, local component finiteness and the
existing relative clopen component identity prove the finite count for
every sufficiently small positive radius. No source correction or
additional numbered-theorem hypothesis is introduced. See the
[section account](../chapter3/3.4.md#item-3-4-9).

### 3.4.10 — Dimension and singular parts (pp. 337–338)

The compact bounds and manifold cover reuse the original corrected
stratification and dimension results of 3.4.8. For the negative example,
[WhitneyBruhat1959](../bibliography.md#whitneybruhat1959), §11(c), p. 159,
gives Cartan's actual polynomial surface $yz(x^2-zy^2)+x^4=0$.
The formal proof verifies its geometry through the project's analytic
inverse, tangent and identity theorems. It does not assume the printed
formula for its full singular locus. See the
[section account](../chapter3/3.4.md#item-3-4-10).

### 3.4.11 — Tangent hulls and homogeneous majorants (p. 338)

The proof reuses the original first nonzero germ jets, the Taylor theorem
of 3.1.11, the Haar comparison and depth laws of 3.4.8, and its completed
relative-open null-dimension theorem (16). The original cusp has equation
$x_1^3=x_2^2$. Its actual positive-half-axis tangent and nonanalyticity
are proved within the project. No additional source or correction is
needed. See the [section account](../chapter3/3.4.md#item-3-4-11).

### 3.4.12 — Complex analytic extension (pp. 338–339)

Use [Federer1969](../bibliography.md#federer1969), pp. 338–339,
with the earlier passages of 3.4.5–11 and the adopted published
corrections to 3.4.8. The project proves the complex extension using
actual complex derivatives, unitary Haar reductions, and paired real
coordinates. The independent dimension comparison corrects the reversed
factor in the final display on p. 339. The connected punctured square
graph supplies an additional counterexample to carrying over the real
componentwise projection-homeomorphism conclusion. The correct complex
conclusion is a finite covering with local holomorphic sections.
These are project qualifications, not published erratum entries.
The cited external expositions remain bibliographical source accounts;
their contents are not claimed formalised. See the
[section account](../chapter3/3.4.md#item-3-4-12).

## Consulted passages: Chapter 4

### 4.1.1 — Test functions and distributions (pp. 343–346)

[Federer1969](../bibliography.md#federer1969) gives the exact derivative
seminorms, support definitions, weak duals, literal final test topology,
restriction maps, derivatives and integral-distribution formula.
[Menne2016](../bibliography.md#menne2016), Definition 2.13 and Remarks
2.14–2.17, p. 996, distinguishes this final topology from the locally
convex inductive topology. The two have the same continuous linear maps
into locally convex spaces. The formalisation proves this comparison for
the actual compact-support test steps and uses the original topology in
the quotient-limit theorem.

The zero-dimensional counterexample to the p. 344 nonembedding sentence
is a project finding, absent from Federer's erratum. See the
[section account](../chapter4/4.1.md#item-4-1-1) and
[error catalogue](federer-errors.tex).

The user also supplied [Bourbaki1987](../bibliography.md#bourbaki1987) and
[Schwartz1973](../bibliography.md#schwartz1973) for the topological-vector
and Radon-measure foundations. The supplied Bourbaki copy remains
unreadable; no passage from it is claimed consulted. Schwartz's text has
been extracted; its specific proof use will be recorded under the item
concerned. The original Radon and vector Daniell results proved in
Chapter 2 supply the representation theorem in 4.1.5.

### 4.1.5 — Representation by integration (pp. 349–350)

Both original printed pages were read visually. The formalisation keeps
Federer's gauge on positive compact continuous scalar tests, proves its
convolution extension and sharp bound, and identifies it with the original
Daniell variation and its Radon measure in the finite-gauge case. The
original L1 extension, simultaneous characteristic-ball formula, scalar
Daniell variation, weak lower semicontinuity and monotone-bound compactness
are included. See the [item account](../chapter4/4.1.md#item-4-1-5).

[Menne2016](../bibliography.md#menne2016), Definition 2.18 and Remark 2.19,
p. 997, distinguishes its general largest Borel regular variation measure
from Federer's original scalar-test gauge outside the Radon case. The
formalisation preserves that distinction; it assigns the original Radon
variation only after proving the finite-gauge criterion. The test topology
remains Federer's literal final topology. No unpublished lecture notes
are used or cited. The unreadable Bourbaki copy supplies no claimed
passage, and no new Schwartz passage is claimed for this proof.

### 4.1.6 — Differential forms (pp. 351–355)

All five original printed pages were read visually. The formalisation
follows the pointwise algebra, coordinate expansion, exterior derivative,
graded product rule, square-zero argument, divergence and duality sign.
The pullback commutation proof uses the original coordinate generators.
The general normed-coefficient case follows by bounded norming functionals
and the earlier separation theorem. See the
[item account](../chapter4/4.1.md#item-4-1-6).

The earlier tensor, exterior and multilinear results supply the algebra
and exact induced norm. The original second-differential theorem supplies
symmetry without continuity of the second derivative. No new passage from
the unreadable Bourbaki copy or from Schwartz is claimed consulted, and no
unpublished lecture notes are cited.

### 4.1.7 — Currents, mass and proper pushforward (pp. 355–359)

All five original printed pages were read visually. The formalisation
retains all eight current identities, the original partial ball orientation,
exact variation, both local normality criteria and support-proper
pushforward. The class-one boundary formula keeps the original unrestricted
form. Bounded Baire projection and relative Borel restrictions use the
original orientation weight. See the [item account](../chapter4/4.1.md#item-4-1-7).

On p. 359 the boundary equation alone does not determine the whole-line
primitive. The original left primitive and a negative right primitive give
actual distinct currents with the same boundary. Agreement with the interval
current on the open half-line supplies the intended uniqueness condition.
The support obstruction is proved independently. This project correction
is absent from the published erratum. The printed sign on p. 357 is correct.
The proof reuses the preceding current, distribution, Radon and calculus
results; no new passage from Bourbaki or Schwartz is claimed consulted.

### 4.1.8 — Cartesian products of currents (pp. 360–362)

All three original printed pages were read visually. The formalisation
retains every mixed test degree, all three boundary cases, the compact-first
projection, the original Radon product density and both variation bounds.
The printed hypothesis that either orientation is simple gives equality and the original
partial orientation. Segments, point products, finite Stokes and the actual
Euclidean restriction to the ordered open box are included, with the empty
product. See the [item account](../chapter4/4.1.md#item-4-1-8).

The line after the definition of the slice on p. 360 assigns its
second-factor vector to the wrong ambient space: read R^n for R^m.
The formal slice corrects that type and retains every original dimension
and hypothesis. The correction is absent from the repository transcription
of the published erratum. The equality question without simplicity remains
source prose. The proofs reuse the preceding tensor density, fixed-support
continuity bounds, exterior algebra and product integrals. No new passage
from Bourbaki or Schwartz is claimed consulted. The
[registered validation](../checkpoints/4.1.8-validation.json) passes.

### 4.1.9 — Homotopy formulas and affine mass estimates (pp. 363–364)

Both original printed pages were read visually. The formalisation retains
the open time interval, support-cylinder properness, both current identities,
both original compact test restatements and both pointwise form identities.
The represented-current clause uses the exact original partial orientation
weight and literal integral of the actual weighted slice images. All three
affine estimates retain the printed mixed-power coefficient, degree zero
and infinite masses. See the [item account](../chapter4/4.1.md#item-4-1-9).

The published erratum, p. 6, book p. 363 line 2, changes the English
article A to roman type. This is typographical and changes no mathematical
assertion. No new mathematical source error was found in this item. The
proofs reuse the preceding current products, proper pushforwards, point
currents, exterior norm bounds and nonnegative Fubini theorem. No new passage
from Bourbaki or Schwartz is claimed consulted. No unpublished source is used.

### 4.1.10 — Cone primitives and star-shaped domains (p. 364)

The original printed page was read visually and compared with the published
erratum, p. 6, book p. 364 line 11. The latter corrects the current-space
subscript to the compact-test superscript. The formalisation retains the
exact original test class, smooth primitive, compact-current endpoints and
all three current conclusions on every original star-shaped open domain.
The exact compact segment support avoids a uniform enlarged-time hypothesis.
Positive top degree and degree zero remain separate. See the
[item account](../chapter4/4.1.md#item-4-1-10) and
[registered validation](../checkpoints/4.1.10-validation.json).

The proofs reuse the immediately preceding homotopy identities, actual zero
extension, compact smooth-current extension, current restriction and
above-dimension exterior algebra. No new mathematical source error was
found. The final homology pointer remains commentary. No new passage from
Bourbaki or Schwartz is claimed consulted; no unpublished source is used.

### 4.1.11 — Joins and oriented simplexes (pp. 364–366)

All three printed pages were read visually. The formalisation retains every
original mathematical paragraph: the compact-current join and all boundary
cases, signed interchange, affine naturality, exact mass coefficient, point
cones, simplex boundary and orientation, affine parametrisation, prism and
factorial rectangle decompositions, and associativity. The latter follows
the original barycentric maps and common triangle. See the
[item account](../chapter4/4.1.md#item-4-1-11) and
[registered validation](../checkpoints/4.1.11-validation.json).

The proofs reuse the preceding Cartesian product, proper pushforward,
exterior algebra, point-current and cone laws. Algebraic assertions retain
arbitrary compact currents; mass assertions retain the printed integral
representation hypotheses. Dimension zero and degenerate vertices remain
included. No new mathematical source error was found. No new passage from
Bourbaki or Schwartz is claimed consulted; no unpublished source is used.

### 4.1.12 — Flat seminorms and flat chains (pp. 367–369)

All three printed pages were read visually. The formalisation retains the
original form and current seminorms, the attained mass minimum, flat-chain
closure and completeness, the local criterion, support-neighbourhood
localisation, boundary and multiplier estimates, both Cartesian estimates
and both in-book counterexamples. The weighted example retains its exact
support bound, mass, cutoffs, test values and unbounded harmonic action.
See the [item account](../chapter4/4.1.md#item-4-1-12) and
[registered validation](../checkpoints/4.1.12-validation.json).

The proofs reuse the preceding Hahn–Banach theorem, seminorm bounds,
normal-current mass and boundary laws, compact cutoffs and Cartesian laws.
The dyadic example's support obstruction follows from preceding local
normality and compact top-degree results. These supply the original claim
for which the book anticipates 4.1.18.
The finite-mass nonflat example anticipated here is proved in
[4.1.15](../chapter4/4.1.md#item-4-1-15), including its actual bounded-derivative
smooth approximation and both nonconvergent image degrees. No new
mathematical source error was found in 4.1.12. No new passage
from Bourbaki or Schwartz is claimed consulted; no unpublished source is
used.

### 4.1.13 — Flat estimates for smooth images (pp. 369–370)

Both printed pages were read visually. The original proposition assumes
only that the union of affine segments over the current support lies in
the target. Its proof chooses a smaller source neighbourhood, applies the
preceding homotopy formulas and estimates both deformation-chain masses
by the final inequalities of 4.1.9. The separate zero-degree statement has
only the displacement integral. See the
[item account](../chapter4/4.1.md#item-4-1-13).

The formalisation follows that argument and retains the exact original compact
set, maps, derivative maximum and variation measures. It reuses the
preceding test zero extension, normal-current support and mass laws,
proper pushforward, Radon density variation, compact-product neighbourhoods
and image integration. No new mathematical source error was found. No
new passage from Bourbaki or Schwartz is claimed consulted; no unpublished
source is used. The [registered validation](../checkpoints/4.1.13-validation.json) covers the complete numbered scope.

### 4.1.14 — Lipschitz images of flat currents (pp. 370–372)

All three printed pages were read visually. The item defines compact
Lipschitz images through every allowed smooth approximation, constructs
normal limits, and extends the operator to the original complete flat
spaces. Its second page gives the proper local cutoff definition and
formal properties. The last assertions concern continuous
Lebesgue-almost-everywhere derivative majorants, affine deformation bounds
and evaluation of every continuous form under a class-one map. All these
assertions belong to the numbered item. See the
[item account](../chapter4/4.1.md#item-4-1-14).

The formalisation reuses the preceding source restriction, exact Radon
variation transport, normal-current estimates, complete flat spaces,
compact Lipschitz extension and convolution laws. Each prescribed
relatively compact source admits the required family; the independent
image law retains every original K-only bounded family. The local
operator uses every admissible scalar cutoff and properness only on
actual support. The weighted clauses retain the original variation
measures and Lebesgue-almost-everywhere hypothesis; the class-one identity
permits every continuous target form. No new mathematical source error
was found. The [registered validation](../checkpoints/4.1.14-validation.json)
covers the complete original numbered scope.

### 4.1.15 — Support coincidence and flat-current supports (pp. 372–373)

Both printed pages were read visually. The formalisation keeps the
original radial shrink map, both squared-norm calculations, its
nonexpansion and the ambient agreement map. The proof uses genuine
convolution with one common normalized kernel. The closed-ball agreement
locus, its open local domain, fixed-radius capture and simultaneous
two-parameter errors retain the original bounds. Compact target margins
supply an original-target-valued source neighbourhood internally.

The final support-coincidence law requires equality only on the actual
support of the flat current. Compact retraction localisation, the two
point-support formulas, all three section-image sets and the arbitrary
affine-plane obstruction follow from the preceding actual image laws.
No normality, finite mass or flat index equal to the support is assumed.

The example is the actual one-current $\delta_0\wedge e_1$ on the line.
Its support is one point, its mass is one and its derivative boundary has
infinite mass. Its different images under identity and the zero map
prove nonflatness and complete the forward reference in 4.1.12. Genuine
compact smooth scalar tests tend uniformly to zero with one common
derivative bound and alternating derivatives at zero. Their degree-one
images have no weak limit; the pushed boundaries give the corresponding
degree-zero statement.

The final sentence on p. 373 prints $\mathscr D_0(\mathbb R)$ for images
of a one-current. The intended target is $\mathscr D_1(\mathbb R)$, since
smooth pushforward preserves degree. This local correction is absent
from the published erratum. It is recorded in the
[error catalogue](federer-errors.tex) and the
[divergence register](../divergences.md). See the
[item account](../chapter4/4.1.md#item-4-1-15) and
[registered validation](../checkpoints/4.1.15-validation.json).
No new passage from Bourbaki or Schwartz is claimed consulted; no
unpublished source is used.

### 4.1.16 — Convex retractions and flat norms (pp. 373–374)

Both printed pages were read visually. The nearest-point relation is
specified independently, existence is proved from the preceding closed-set
theorem, and the resulting map is opaque. Its graph is precisely the
original distance-minimising relation. The full segment square, its
minimum at zero, both variational inequalities and the pair inequality
give the original Lipschitz bound one. The convex set is nonempty and
closed; it may be unbounded. The ambient dimension may be zero.

The actual current conclusions use the precise convex hull of the support.
This hull is compact, and the current belongs to its indexed flat space.
The flat norm there equals the flat norm at every larger compact index.
Empty support is handled before choosing a nearest-point map; its convex
hull stays empty. No normality, finite mass or membership indexed by the
unconvexified support is added. Actual endpoint assertions retain the zero
current, empty hull and a nonzero point current in zero ambient dimension.

The ambient space on p. 373, line 29 is $\mathbb R^n$, as corrected in
Federer's [published erratum](federer-erratum.tex), p. 6. This published
misprint is separate from the local degree correction in the preceding
item. No new source error was found. The parenthetical positive-reach
pointer remains outside-source commentary. See the
[item account](../chapter4/4.1.md#item-4-1-16),
[registered validation](../checkpoints/4.1.16-validation.json) and
[error catalogue](federer-errors.tex). No unpublished source is used.

### 4.1.17 — Mass approximation and summable contractions (p. 374)

The printed page was read visually. Both original mathematical paragraphs
are retained: the exact normal mass-closure equality and contraction by
every original variation-summable differential form. The first proof uses
the preceding attained normal filling. The approximant is $Q+\partial S$,
as specified in Federer's [published erratum](federer-erratum.tex), p. 7,
book p. 374, line 16. This is a published proof correction; no new local
source error or counterexample is claimed.

The second proof follows the original smooth approximation argument. The
earlier graded boundary identity supplies normality of smooth
contractions. Compact test bounds give flat continuity, and the original
smooth test density gives $L^1$ approximation for the actual variation.
The original measurable contraction then follows by mass approximation
in the same compact index. The final statement derives representation
and local summability from the original assumptions and permits
unbounded, nonsmooth coefficients without compact support. The separate
density law preserves conull partial coefficient domains.

Both zero-degree endpoints and empty domains or compact indices remain.
The actual nonzero point current in $\mathbb R^0$ checks the singleton
mass closure, its failure for the empty index, and scalar unit
contraction. See the [item account](../chapter4/4.1.md#item-4-1-17),
[registered validation](../checkpoints/4.1.17-validation.json) and
[error catalogue](federer-errors.tex). No unpublished source is used.

### 4.1.18 — Smoothing and compact L1 representations (pp. 374–377)

All four printed pages were read visually. The final kernel-closure
paragraph on p. 377 belongs to 4.1.18 despite the running page header.
Every in-book mathematical assertion is retained. No new source error
was found, and the error catalogue gains no new entry for this item.

The smoothing formulas retain the original reflected kernel
$\Phi_\epsilon(-z)$; its defining laws do not assume evenness. The actual
translation deformation, current and form homotopies, sharp mass and
support bounds, compact flat error and weak variation convergence use
the preceding book interfaces. The averaged variation is an actual
Radon measure, with comparison on every set. The represented current
need not have compact support or finite total mass.

The two original pair propositions keep every compact index, the exact
radius-$\delta$ support enlargement and cost at most
$\mathbf F_K(T)+\delta$. The second starts with any compact-index flat
current. The proof follows the printed normal approximation, smoothing
residual iteration, common radius-$\delta/2$ support, both infinite sums
and downward degree induction. It does not add normality or finite
mass to the original input. Surjectivity, quotient fibres and top-degree
density are proved for the actual flat-current union.

The raw integral size J is a seminorm under null-set changes. The L1
convergence laws respect almost equality. The literal kernel closure
keeps the original raw pair space, J topology and actual compact-support
representatives. This distinction is not a new error claim. The final
closure has the positive divergence sign from the
previous boundary convention; both inclusions are proved by smoothing
and closed-kernel continuity.

The actual nonzero point current in $\mathbb R^0$ checks smoothing,
unit-mass top-degree representation and the quantitative pair with zero
next-degree coefficient. The general statements retain empty domains
and compact sets and every original degree case. See the
[item account](../chapter4/4.1.md#item-4-1-18),
[registered validation](../checkpoints/4.1.18-validation.json) and
[error catalogue](federer-errors.tex). No unpublished source is used.

### 4.1.19 — Flat cochains and measurable forms (pp. 377–378)

Both printed pages were read visually. The mathematical assertions are on
p. 377; the continuation on p. 378 is historical commentary. The preceding
kernel-closure paragraph on p. 377 belongs to 4.1.18. Every mathematical
group of 4.1.19 is retained: the common cochain bound, norm, coboundary,
compact L1 pair functional, signed unit-ball supremum, measurable
representation and its almost uniqueness, weak equation, converse,
class-one and smoothing criteria, and the coboundary pair.

The literal global comass in 4.1.7 is a pointwise supremum. It remains
unchanged. Arbitrary measurable representatives require the essential
norm formula; selected representatives recover the printed global formula
on nonempty U. The actual zero-cochain singleton-spike counterexample
proves that distinction. The smooth zero first form with a one-form null
spike proves that the class-one parenthesis needs almost equality unless
the second form is continuous. Neither correction appears in the supplied
published erratum. The two entries belong in the project's error catalogue,
not in its transcription of Federer's list.

The least-bound convention is explicitly nonnegative, consistently with
the preceding norm conventions. The empty-domain literal global comass is
minus infinity, while the cochain norm is zero. Original smoothing
convolutions are evaluated where their closed kernel balls lie inside U;
no equation is asserted across the boundary of a zero extension. These
are endpoint and domain qualifications, not further source-error entries.
No additional external source is claimed consulted. See the
[item account](../chapter4/4.1.md#item-4-1-19),
[registered validation](../checkpoints/4.1.19-validation.json) and
[error catalogue](federer-errors.tex). No unpublished source is used.

### 4.1.20 — Integral-geometric null support (p. 378)

The entire original item on printed p. 378 was read visually. Its single
assertion is the positive-degree null-support theorem for the exponent-one
integral-geometric measure. The proof uses the original 2.10.5 and 1.7.4
rotation step, the 4.1.6 coordinate expansion and the 4.1.18 top-degree
flat-current representation. The final statement retains arbitrary open
source domains and adds no finite-mass or normality premise. No new source
error or additional external source is claimed. See the
[item account](../chapter4/4.1.md#item-4-1-20) and
[registered validation](../checkpoints/4.1.20-validation.json).

### 4.1.21 — Null-set corollaries for flat currents (p. 378)

The entire original item on printed p. 378 was read visually. Both
corollaries use the preceding null-support theorem. The first retains an
arbitrary original B and the printed relative closedness of support minus
B. Its compact scalar cutoff has no mass or representation premise. The
second retains an arbitrary original E: Borel regularity supplies a null
hull before the actual Radon variation is reduced to compact subsets.
Finite mass supplies the representation. Compact measurable restriction,
exact support and exact mass close the argument. No new source error or
additional external source is claimed. See the
[item account](../chapter4/4.1.md#item-4-1-21) and
[registered validation](../checkpoints/4.1.21-validation.json).

### 4.1.22 — Integral and real polyhedral chains (p. 379)

The entire original item on printed p. 379 was read visually. It defines
the fixed-index integral subgroup generated by oriented simplexes whose
full vertex hull lies in K, its real algebraic span, and the two unions
over all compact subsets of the original open U. The formalisation uses
the actual simplex currents of 4.1.11. Independent generation laws and
opaque carriers retain the original group and vector-space structures.
Normality, fixed-index support, flatness, boundary and open restriction
are proved for use by the following items. No additional external source
or new source error is claimed. See the
[item account](../chapter4/4.1.md#item-4-1-22) and
[registered validation](../checkpoints/4.1.22-validation.json).

### Polyhedral approximation in 4.1.23

The account of 4.1.23 retains the printed theorem and all five proof
reductions on pp. 379–380, including the transverse atomic error and exact
rectangular mass identity. It adds no source-error entry. The reference
to 4.2.24 remains a later normal-mass approximation obligation.

### Integral currents in 4.1.24

The whole item on printed pp. 380–382 was read visually; the published
erratum has no entry for these pages. The account retains the literal
mass-approximation definition of rectifiable currents, the separate
degree-zero integral clause, every inclusion of the diagram, the local
germ classes, the integral flat infimum and its complete metric, the
series estimate and the final flat decomposition with its attained flat
filling. Integer coefficients are retained throughout. The attained
integral minimum of 4.2.18 and the characterisations of 4.1.28 remain
forward references. No new source error is claimed. See the
[item account](../chapter4/4.1.md#item-4-1-24) and
[registered validation](../checkpoints/4.1.24-validation.json).

## English writing

The user requires strict adherence to [Strunk2011](../bibliography.md#strunk2011)
for all English prose in this project. The supplied electronic copy contains
William Strunk, Jr.'s text, including the eighteen numbered rules of usage
and composition, the sections on form, word choice, and spelling, and the
exercises. Apply the guide to comments,
documentation, reports, replies, and commit messages.

The supplied edition was reviewed again for the
documentation reorganisation. See the [writing rules](../maintenance.md#english-and-mathematical-language).
