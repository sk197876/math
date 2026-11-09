# Source consultation guide

[Documentation](../toc.md) · [Item map](../contents.md) · [Index](../index.md) · [Symbols](../symbols.md) · [Divergences](../divergences.md) · [Bibliography](../bibliography.md)

## Contents

- [Editions and corrections](#editions-and-corrections)
- [Annotation validation](#annotation-validation)
- [Consulted passages: Chapter 2](#consulted-passages-chapter-2)
- [Consulted passages: Chapter 3](#consulted-passages-chapter-3)
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
incorporate the 1987 corrections). The list was synchronized on 4 November
2026 through the validated work in 3.2.48, with the deferred and partial
items explicitly excluded from completion claims. It includes the later
local corrections in 3.2.37, 3.2.38 and 3.2.46, and a separate section for
the convention-dependent line endpoints of 3.2.42–3.2.44.

An editorial note also distinguishes the raw Steiner power from the
normalized quotient in the erratum's p. 5, book p. 275 line 2 replacement.
The scan prints `r^(n-j)`; division by the original `alpha(n-m) r^(n-m)`
leaves `r^(m-j)`. This note does not claim an additional kernel-checked
counterexample. The erratum transcription preserves the scan.
The compiled PDFs are not tracked.

The catalogue was reorganised on 9 November 2026. It retains all 123
earlier entries and adds five published Chapter 3 corrections: two
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
changes and their validation have separate dated records.

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
The integer Hausdorff and spherical specialisations also check, including
boundedly compact spaces without a supplied finite-mass support cover.
[`spherical_weighted_proper_equality`](../../theories/SphericalProperWeighted.v#L59)
repairs the false closed-family justification by the existing Hausdorff
comparison. The Gross and integral-geometric applications in the final
paragraph of p. 188 are proved for arbitrary nonnegative extended inputs;
real-degree Hausdorff/spherical extensions remain pending.

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
counterpart. No working- erratum entry applies to p. 201. Both private graph
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
The private recovery material for the incomplete Kneser example is
excluded from this public snapshot.
The user deferred the second example on 2 November 2026; it is not a
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
remains an explicit later obligation.

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

## English writing

The user requires strict adherence to [Strunk2011](../bibliography.md#strunk2011)
for all English prose in this project. The supplied electronic copy contains
William Strunk, Jr.'s text, including the eighteen numbered rules of usage
and composition, the sections on form, word choice, and spelling, and the
exercises. The text was read on 5 November 2026. Apply the guide to comments,
documentation, reports, replies, and commit messages.

The supplied edition was reviewed again on 9 November 2026 for the
documentation reorganisation. See the [writing rules](../maintenance.md#english-and-mathematical-language).
