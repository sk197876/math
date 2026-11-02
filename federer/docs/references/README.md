# Source consultation guide

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

[federer-errors.tex](federer-errors.tex) lists the statements of the book
that the formalisation refutes and that Federer's list does not correct,
together with proposed corrections, the error in the list itself, and the
corrections of the list adopted here. Each entry was checked against the
printed text of the 1969 edition (Springer reprint, which does not
incorporate the 1987 corrections). Its compiled PDF is not tracked.

Compile the reference without building Rocq or writing generated files here:

```sh
mkdir -p /tmp/federer-erratum-build
pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory=/tmp/federer-erratum-build docs/references/federer-erratum.tex
```

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

## Federer 2.10.20: supporting continuity and open-envelope passages

The four target assertions are on book pp. 181–182. That lemma leaves its
proof as an exercise; the project already proves and seals the envelope used
here. Do not attribute the four identical radial/compact assertions to these
passages. No erratum entry concerns book pp. 181–182.

## Federer 2.10.21: metric profiles and compact convex hulls

The target spans book pp. 182–184. Apply erratum p. 3, book p. 184 lines 8 and
10, to the scope of the final convex density assertion: its ambient sets are
nonempty compact convex sets. The project uses its own proved dimension
reduction and compact parameter images, directly in the supplied norm
topology.

## Federer 2.10.22: compact-cost continuity below

The complete target and proof occupy book pp. 184–186. Its cost is finite,
nonnegative and Hausdorff-continuous, with strict positivity only required on
positive diameters. Positive singleton costs remain permitted. No correction
to this item occurs in the working erratum. The proof uses 2.10.20 radial
exhaustion and 2.10.21 Hausdorff compactness. [Kelley2017](../bibliography.md#kelley2017)'s cited diagonal process
is printed p. 238, Problem D(a), in the local Dover 2017 reprint of *General
Topology* (1955). The formal proof uses instead a compact-product cluster
point and finite-coordinate neighbourhoods at arbitrarily late rows. No
identical compact-cost continuity theorem was located there Cost ordering,
inactive cover positions and finite-prefix residual bounds are project proof
expansions, recorded separately from Federer's statement and from his erratum.

## Federer 2.10.23: compact inner approximation of Suslin sets

Read the complete corollary and proof on book p. 186, the cited
coordinate-pruning and compact-fibre argument in 2.2.12, pp. 68–69, and the
compact-intersection inequality of 2.10.20, p. 182. The working erratum has no
correction to this corollary. The formal proof uses continuity below from
2.10.22 for cutoff measures. It derives the needed open-envelope comparison
directly from cost continuity; it does not claim the stronger interior-cost
infimum equality follows for nonmonotone continuous costs. No identical
compact-approximation corollary was located. The half-error geometric budget
is the same proved strengthening already recorded for the project's 2.2.12.

For the weighted-cover item 2.10.24, pp. 186–188, both numbered criteria and
the general inequality are checked. The local counterexample
[`closed_ball_hausdorff_closedness_counterexample`](../../theories/ClosedBallHausdorffApproximation.v#L129)
refutes the p. 188 auxiliary closed-ball-family remark in a compact real
subspace. It is separate from the erratum's script-S correction (erratum p. 4,
book p. 188 line 21), and does not disprove the spherical integral equality.
The integer Hausdorff and spherical specialisations now also check, including
boundedly compact spaces without a supplied finite-mass support cover.
[`spherical_weighted_proper_equality`](../../theories/SphericalProperWeighted.v#L59)
repairs the false closed-family justification by the existing Hausdorff
comparison. The Gross and integral-geometric applications in the final
paragraph of p. 188 are now proved for arbitrary nonnegative extended inputs;
real-degree Hausdorff/spherical extensions remain pending.

The supporting weighted projection-cover estimates for 2.10.24, p. 188, read
the actual gauge definitions 2.10.4(1) and 2.10.5(1), pp. 172–173, and the
norm formulas and seminorm assertion 2.4.12, pp. 86–87. The estimates are
intermediate results supporting the two final weighted-integral applications
now proved below.

The Borel-indicator step toward the final paragraph of 2.10.24, p. 188, uses
the full Borel partition supremum of 2.10.8, p. 175, and the metric criterion
2.3.2(9), p. 75. The restricted weighted measure and its abstract supremum
specification are local supporting infrastructure, not additional claims
attributed to those sources.

The complete Gross and integral-geometric applications in the final paragraph
of 2.10.24, p. 188, now use the exact Borel-partition supremum of 2.10.8, p.
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

For 2.10.25, pp. 188–189, the actual fibre estimate and proof were read in
Federer. No matching substantive correction appears in the working erratum;
the book p. 188 line 21 entry on erratum p. 4 changes only script S in
2.10.24. Infinite intermediate grouped weights are a local proof
clarification, not Federer's correction.

For 2.10.26, pp. 189–190, the actual statement and the p. 190 scan were read.
The strict V_j cover budget is t+1/j; text extraction omitted that slack.
There is no corresponding erratum entry for pp. 189–190. Federer 2.2.3–2.2.4,
pp. 61–62, supply compact approximation and the nonmeasurable-set existence
argument. they are not attributed the identical fibre theorem or inclusion
example. The historical questions and topological-dimension discussion remain
source context.

For 2.10.27, pp. 190–191, both scanned pages were read. The projection
identity on p. 191 prints an open base ball for a closed source ball; the
formalisation proves the closed-ball identity and an explicit boundary
counterexample. This local correction has no matching entry in the working
erratum. Source-indexed cost sums retain repeated sections instead of relying
on injectivity of the printed family H(y). The zero-dimensional extension is a
project convention, not a claim of that example.

For 2.10.28, pp. 191–193, all three Federer scans were read. That condition is
Federer's own correction, erratum p. 4, book p. 192 line 4. The p. 193 line 7
sum index is also corrected there.

For the in-progress 2.10.29, pp. 193–195, the p. 194 scan was read directly.
The working erratum p. 4, book p. 194 line 8, corrects the last interleaving
term to sigma_j>=t_(j+1)->0. The present explicit-coefficient interfaces do
not assume Euler-Gamma normalisation.

The 2.10.29 product proof now includes both local cases on Federer p. 194,
the direct covering-infimum infinity argument, and the finite square covers
on p. 193. The Euclidean plane uses the existing block and scalar
coordinate interfaces. The positive finite-power paragraph on p. 195, including its actual
orthogonal coordinate identification, is now proved for explicit
normalising coefficients. Analytic Gamma normalisation remains pending.

The positive finite-power proof for 2.10.29, p. 195, now uses finite
coordinate-box covers with conserved weights, and products of vanishing local
densities. The latter expands the printed reference to 2.10.27. The final
coordinate permutation is specified by inverse, squared-distance and
membership laws; its recursive witness stays private.

For Federer 2.10.30, printed p. 195, the actual passage and the working
erratum were checked. The formalisation retains Federer's compact-source
volume statement and separately proves compactness, convexity and the
boundary-sphere exclusion.

For Federer 2.10.31, printed pp. 195–196, both actual page scans were checked.
The p. 196 inference following the reflected-cap formula really prints B(a,s),
s<r. The formalisation records a local correction to centre zero and a
concrete singleton obstruction to the printed-centre inference. The May 1987
erratum p. 4, book p. 195 line 20, only changes punctuation and has no entry
for p. 196. its subsequent coordinate-iteration isodiametric argument is not
cited as a proof of 2.10.31.

For Federer 2.10.32, printed pp. 196–197, the actual page scans and the
working erratum were checked. Erratum p. 4, book p. 197 line 4, corrects the
raw endpoint bound to mu*alpha(m)^(-1)*2^m (the proof works in R^m); the final coefficient in the
theorem is unchanged. The planar unit-ball regression gives exterior supremum
at least four and diameter at most two. This supporting-source wording
correction is separate from Federer's erratum. The exterior norm passages were
verified separately. They supply algebraic background, not the measure
theorem.

For Federer 2.10.33, printed p. 197, the actual book scan. the project follows
Federer's short deduction from 2.10.32 and 1.7.5. The two independently
verified editions' exterior norm references are those recorded for 2.10.32
above. The working erratum has no additional correction to this corollary.

For Federer 2.10.34, printed p. 197, use the actual displayed projection chain
and the compact-cover alternative of 2.10.3, p. 172. These are algebraic
supporting references and do not state the Gross comparison. No additional
working-erratum correction applies to this corollary.

For Federer 2.10.35, printed p. 197, the actual scan and working erratum were
checked. the project retains Federer's density argument for the upper
spherical bound. The other four measure equalities use the actual
full-dimensional projection volume and beta_t(n,n)=1. No additional
working-erratum correction is needed for this item.

For Federer 2.10.36, the actual printed p. 198 was checked, including the
normal projection, exterior-factor comparison, Steiner hull inclusion and
height-times-base volume bound. The scalar calculation behind the last
comparison also uses the actual simplex passage of 2.7.16, p. 136. No
correction for p. 198 occurs in the working erratum. The compact reduction and
use of the sufficient norm inequality are recorded as proof-route expansions,
separately from source corrections.

For Federer 2.10.37, the actual printed p. 198 and the projection-norm
identity of 2.7.16(6), p. 140, were checked. The degree-one coefficient uses
alpha(1)=2 as printed in 2.7.16(1), p. 135. No relevant working- erratum
correction applies. The intermediate Suslin premise ensures measurable norm
inputs on the original open convex generator family; it adds no target
hypothesis to the corollary.

For Federer 2.10.38, the actual printed pp. 198–199 and the box inequalities
in 2.7.16, p. 136, were read. The working erratum has no entry for pp.
198–199. The missing nonempty-source qualification is a local correction, with
an explicit empty-compact counterexample. The intrinsic finite-prefix
implementation follows the same maximal projected-chord induction as the
book's successive coordinate projections; its implementation is hidden and all
downstream geometric properties are derived from the abstract laws.

For Federer 2.10.39 the printed proof on p. 199 and the degree convention of
2.10.3, pp. 171–172, were read. The latter does not restrict m to n;
above-ambient degrees are included by the dimension-drop argument in 2.10.2,
p. 171, and ambient-degree equality in 2.10.35, p. 197. The working erratum
has no entry for p. 199. Positive enlargements and finite-product continuity
fill in the degenerate-box case left implicit by the book's positive-width
preliminary argument; they are an expanded proof, not an attributed erratum
correction.

For Federer 2.10.40 the actual printed pp. 199–200 were read. No relevant
working-erratum entry applies to pp. 199–200. The formal contact limit uses
nested closed reciprocal constraints in compact P instead of a convergent
subsequence. An explicit uniform-slack proof supplies contact nonemptiness
even when there are no unit directions in ambient dimension zero.

For Federer 2.10.41 the actual printed proof on p. 200 was read. The formal
finite support proof reuses local coefficient elimination after translating
one generator to zero; at most n+1 points suffice, without padding or an
affine-independence assertion. No relevant working-erratum entry applies to p.
200.

For Federer 2.10.42 the actual statement on printed p. 201 was read. The
formal interfaces currently use natural degrees. Independent cutoffs t and
t/(q+1) keep the Jung ball diameter strictly within the spherical cutoff
before final suprema. No working-erratum entry applies to book p. 201.

For Federer 2.10.43 the actual printed proof on p. 201 was read. The formal
proof allows nonnegative coefficients and repeated contact points: a strictly
positive weighted squared-distance source budget replaces pruning and the
split between one and several contacts. it has no extension-theorem
counterpart. No working- erratum entry applies to p. 201. Both private graph
and scaling witnesses are hidden by opaque
[KirszbraunExtensionSealed.v](../../theories/KirszbraunExtensionSealed.v);
downstream results use only agreement and global-bound laws.

For Federer 2.10.44 the actual printed p. 202 was read. No working-erratum
entry applies to book p. 202. The distance-two sentence is locally qualified
to distinct points; the finite infimum formula needs a nonempty source on an
inhabited ambient space. Both qualifications have proved counterexamples and
are separate from Federer's published corrections. The older 2.5.9
scalar-construction header is corrected only in its comments to cite the
formula's later printed appearance in 2.10.44.

For Federer 2.10.45 the actual printed pp. 202–203 were read. No relevant
entry occurs in the working erratum. The local repair for diameter-zero
generators uses positive mesh limits, not positive-diameter enlargements in an
arbitrary metric factor. Natural degrees are covered; the common
Gamma-normalised real-degree extension remains pending.

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

For Federer 3.1.1, the actual passage on printed pp. 209–211 was read.
The differential requires an interior domain point and a continuous linear
approximation. The real-source and gradient cases are on p. 209, as is
the local inverse rule (1); the chain and linear rules (2)–(3) are on
p. 210. The gradient paragraph refers back to the polarity and complete
inner-product representation developed in Chapter 1. The erratum, p. 4,
book p. 210 line 26, reverses the difference in the inverse-function
iteration: u_(n+1)-u_n = g(u_(n-1))-g(u_n). This correction is applied in the completed inverse-function proof; it
does not change the opening differential or local inverse statements.

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

For Federer 3.2.1 the actual printed p. 241 was read. It defines the
ordinary and approximate k-dimensional Jacobians by exterior operator
norms and introduces a roadmap to subsequent area/coarea theorems. The
latter are not assumed in the Jacobian interface. No retained erratum
entry applies to p. 241. The next item must apply erratum p. 4, book
p. 242 line 23, correcting the direction of the orthogonal map in the
polar factorization to O(n,m).

For 3.2.40, printed p. 276, the local published sources
[Gross1918](../bibliography.md#gross1918), pp. 184–187, and
[Kneser1955](../bibliography.md#kneser1955), Satz 5, pp. 386–387,
were consulted. The Cantor-square and Kneser drafts are excluded from this validated source snapshot.
The user deferred the second example on 2 November 2026; it is not a
completed formalisation. Neither source supplies an assumed theorem or
new project axiom in the registered development.
