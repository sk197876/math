# Verification and release records

[Documentation](toc.md) · [Item map](contents.md) · [Index](index.md) · [Symbols](symbols.md) · [Divergences](divergences.md) · [Bibliography](bibliography.md)

## How to read the records

Compilation, recursive kernel checking, and assumptions audits establish
the recorded statements under their recorded hypotheses. Coverage and
source qualifications remain part of each [section account](toc.md).
A historical validation does not validate later changes or private drafts.

The historical accounts retain release descriptions once spread through
the project README and documentation index, through the initial
release of 3.4.6. Newer items have separate registered validation records
below. A later completion claim requires its own checked sources and record.

## Latest full-project validation

The latest full-project validation compiled all 11,288 registered sources
normally in a new artifact tree. The rebuild passed
in 59504.91s. Complete recursive kernel checking
passed in 1263.92s; extra roots covered every
registered module outside the standard public and example closures.
The fresh full assumptions audit passed in 37133.15s.
All 27,787 queries were rerun, every earlier assumption set
was preserved, and only the three permitted boolp assumptions occurred.

The proof inputs stayed fixed. Validation
used switch RP.2026.02.0~9.1~2026.01, nice 10, umask 0002, group llm,
group read/write, and up to eight compiler workers with memory admission.
It used a fresh directory under /opt/rocq/federer-build, without cleaning
the active tree, adopting another checkout, or copying proof objects.
Compilation, kernel checking, and the full audit ran in sequence.
The run started after 17:00 Europe/Warsaw and retained the documented
deferrals. The stronger real compact-union assertion in 3.4.8(5) has a
separate successful supplement; the real proof does not certify a stronger
complex analogue.

Before this fresh run, one terminal empty line was removed from
[FieldBlockLinear.v](../theories/FieldBlockLinear.v). No mathematical token changed. The report records
both hashes; the complete fresh validation checked the final bytes.

See the [full validation report](checkpoints/chapter3-full-validation.json).

## Latest coverage supplement

The supplements below complete the requested coverage gaps. Each record
preserves the earlier assumption sets and records its own fixed inputs.
Only the three permitted `boolp` assumptions occur. The
[coverage record](checkpoints/coverage-completion.md) lists the user’s
intentional omissions.

### Chapter 1

#### 1.4.4 — Coefficient noninjectivity

The general corrected coefficient noninjectivity assertion of 1.4.4,
p. 20, passes ordinary registered compilation, complete recursive
item/dependency kernel checking in 118.176 seconds, and all ten new
assumptions queries in 66.094 seconds. The actual scalar-line and
zero-source regressions pass. Every one of the 27,787 earlier assumption
sets is preserved; the complete log has 27,797 entries and only the three
permitted boolp assumptions. No earlier mathematical proof source changed.
The incremental build refreshes stale active artifacts from the earlier
validated terminal-line normalization as well as checking the new modules.
No cleaning, adoption or copied proof objects occurred. See the
[item account](chapter1/1.4.md#item-1-4-4),
[validation report](checkpoints/1.4.4-supplement-validation.json), and
[completed coverage record](checkpoints/coverage-completion.md).

#### 1.4.5 — Exceptional cases

The sharp corrected exceptions of 1.4.5, p. 20, also pass. Six theories
and four boundary regressions compile normally in 89.607 seconds.
Complete recursive item/dependency kernel checking passes in 125.501
seconds; all 30 new assumptions queries pass in 79.779 seconds. Every
one of the 27,797 earlier assumption sets is preserved. The complete log
has 27,827 entries and only the permitted boolp assumptions. Two compiler
workers, memory admission and a 1,536 MiB reserve were used; minimum
observed available memory was 2,489.062 MiB. Inputs and base revision
remained fixed. No earlier mathematical source changed, and no cleaning,
adoption or copied proof object occurred. See the
[item account](chapter1/1.4.md#item-1-4-5) and
[validation report](checkpoints/1.4.5-supplement-validation.json).

### Chapter 2

#### 2.10.6 — Measure comparisons and ratios

The 2.10.6 supplement proves all original measure-comparison edges, printed coefficient bounds, bounded and unbounded ratios, actual compact separating examples, and ambient and rectifiable agreements. Its normal registered build passes in 112.06 seconds, complete recursive item/dependency kernel checking in 540.077 seconds, and all 14 new assumptions queries in 152.552 seconds. Every one of the 28,327 earlier assumption sets is preserved. The complete 28,341-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter2/2.10.md#item-2-10-6) and [validation report](checkpoints/2.10.6-supplement-validation.json).

#### 2.10.11 — Multiplicity and the spherical correction

The 2.10.11 supplement proves the original Hausdorff multiplicity theorem in every nonnegative real degree, a compact isometric counterexample to the printed spherical parenthesis, and the corrected spherical bound with factor 2^p. Its normal registered build passes in 262.825 seconds, complete recursive item/dependency kernel checking in 320.379 seconds, and all 52 new assumptions queries in 75.185 seconds. Every one of the 27,987 earlier assumption sets is preserved. The complete 28,039-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter2/2.10.md#item-2-10-11) and [validation report](checkpoints/2.10.11-supplement-validation.json).

#### 2.10.17 — Partial quotients

The 2.10.17 supplement proves the original partial-quotient null-locus assertion of part (3), using the uncut covering measure and every printed hypothesis. Its normal registered build passes in 65.149 seconds, complete recursive item/dependency kernel checking in 196.085 seconds, and all 5 new assumptions queries in 17.035 seconds. Every one of the 27,827 earlier assumption sets is preserved. The complete 27,832-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter2/2.10.md#item-2-10-17) and [validation report](checkpoints/2.10.17-supplement-validation.json).

#### 2.10.19 — Real-dimensional density estimates

The 2.10.19 supplement proves all five original metric-density estimates in every nonnegative real degree, with the actual Gamma normalization and original positive-radius quotients. Its normal registered build passes in 277.86 seconds, complete recursive item/dependency kernel checking in 321.774 seconds, and all 31 new assumptions queries in 96.028 seconds. Every one of the 27,849 earlier assumption sets is preserved. The complete 27,880-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter2/2.10.md#item-2-10-19) and [validation report](checkpoints/2.10.19-supplement-validation.json).

#### 2.10.24 — Weighted-cover applications

The 2.10.24 supplement proves both real-degree Hausdorff and spherical weighted-cover applications, with either a countable finite-measure positive-support cover or a boundedly compact ambient space. Its normal registered build passes in 160.57 seconds, complete recursive item/dependency kernel checking in 318.16 seconds, and all 14 new assumptions queries in 69.152 seconds. Every one of the 27,880 earlier assumption sets is preserved. The complete 27,894-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter2/2.10.md#item-2-10-24) and [validation report](checkpoints/2.10.24-supplement-validation.json).

#### 2.10.25 — Real-dimensional fibre bounds

The 2.10.25 supplement proves the original fibre upper-integral theorem for every nonnegative real pair of degrees, with the actual least Lipschitz constant and exact Gamma coefficient. Its normal registered build passes in 238.144 seconds, complete recursive item/dependency kernel checking in 319.56 seconds, and all 25 new assumptions queries in 104.253 seconds. Every one of the 27,894 earlier assumption sets is preserved. The complete 27,919-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter2/2.10.md#item-2-10-25) and [validation report](checkpoints/2.10.25-supplement-validation.json).

#### 2.10.26 — Fibre measurability

The 2.10.26 supplement proves both original fibre measurability conclusions for every nonnegative real pair of degrees, retaining the boundedly compact source and finite measurable source set while keeping the target arbitrary. Its normal registered build passes in 244.562 seconds, complete recursive item/dependency kernel checking in 319.947 seconds, and all 19 new assumptions queries in 86.8 seconds. Every one of the 27,919 earlier assumption sets is preserved. The complete 27,938-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter2/2.10.md#item-2-10-26) and [validation report](checkpoints/2.10.26-supplement-validation.json).

#### 2.10.27 — Sharp spherical sections

The 2.10.27 supplement proves the original sharp Euclidean spherical section inequality in every nonnegative real degree, including both zero endpoints and arbitrary source sets. Its normal registered build passes in 641.093 seconds, complete recursive item/dependency kernel checking in 320.159 seconds, and all 61 new assumptions queries in 233.144 seconds. Every one of the 28,039 earlier assumption sets is preserved. The complete 28,100-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter2/2.10.md#item-2-10-27) and [validation report](checkpoints/2.10.27-supplement-validation.json).

#### 2.10.28 — Hausdorff normalization of the Cantor application

The 2.10.28 supplement proves the exact Gamma-normalized real-degree Hausdorff identification and the complete original power Cantor application. Its normal registered build passes in 78.592 seconds, complete recursive item/dependency kernel checking in 326.404 seconds, and all 5 new assumptions queries in 40.491 seconds. Every one of the 27,832 earlier assumption sets is preserved. The complete 27,837-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter2/2.10.md#item-2-10-28) and [validation report](checkpoints/2.10.28-supplement-validation.json).

#### 2.10.29 — Cantor products

The 2.10.29 supplement proves all original Cantor product conclusions with their actual Gamma-normalized real-degree Hausdorff measures. Its normal registered build passes in 82.198 seconds, complete recursive item/dependency kernel checking in 336.224 seconds, and all 3 new assumptions queries in 33.071 seconds. Every one of the 27,837 earlier assumption sets is preserved. The complete 27,840-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter2/2.10.md#item-2-10-29) and [validation report](checkpoints/2.10.29-supplement-validation.json).

#### 2.10.42 — Real-dimensional Jung comparison

The 2.10.42 supplement proves the original Jung spherical/Hausdorff comparison in every nonnegative real degree, including its printed coefficient and both zero endpoints. Its normal registered build passes in 141.116 seconds, complete recursive item/dependency kernel checking in 330.587 seconds, and all 9 new assumptions queries in 46.302 seconds. Every one of the 27,840 earlier assumption sets is preserved. The complete 27,849-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter2/2.10.md#item-2-10-42) and [validation report](checkpoints/2.10.42-supplement-validation.json).

#### 2.10.45 — Euclidean-factor products

The 2.10.45 supplement proves the original Euclidean-factor product formula and both printed coefficient bounds for every nonnegative real section degree, retaining arbitrary finite-mass second factors and every Lebesgue-measurable first factor. Its normal registered build passes in 21.854 seconds, complete recursive item/dependency kernel checking in 331.393 seconds, and all 49 new assumptions queries in 224.938 seconds. Every one of the 27,938 earlier assumption sets is preserved. The complete 27,987-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter2/2.10.md#item-2-10-45) and [validation report](checkpoints/2.10.45-supplement-validation.json).

The first registered 2.10.45 build compiled all 26 new files normally in 583.986 seconds. Adding the independent product-lower-bound module as an explicit check root changed only the Makefile. Every proof source stayed fixed; the final registered build, two-root recursive check, and audit passed again on the final inputs.

### Chapter 3

#### 3.2.45 — Quantitative source correction

The 3.2.45 supplement proves the actual unit-segment counterexamples to the printed quantitative estimate, its failure for every finite proposed constant, and the corrected convex secant implication. Its normal registered build passes in 153.758 seconds, complete recursive item/dependency kernel checking in 357.81 seconds, and all 13 new assumptions queries in 106.66 seconds. Every one of the 28,100 earlier assumption sets is preserved. The complete 28,113-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter3/3.2.md#item-3-2-45) and [validation report](checkpoints/3.2.45-supplement-validation.json).

#### 3.2.45 — Exponent continuity

The 3.2.45-continuity supplement proves continuity of the original Q_t(A) on the full extended exponent interval for every target A, with both endpoints and zero or infinite masses. Its normal registered build passes in 738.911 seconds, complete recursive item/dependency kernel checking in 364.253 seconds, and all 69 new assumptions queries in 238.371 seconds. Every one of the 28,215 earlier assumption sets is preserved. The complete 28,284-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter3/3.2.md#item-3-2-45) and [validation report](checkpoints/3.2.45-continuity-supplement-validation.json).

#### 3.2.45 — Gillespie product upper bound

The 3.2.45-product-upper supplement proves the original Euclidean-factor Gillespie product upper inequality for arbitrary factors, with infinite second-factor masses on the ordinary partial-product domain and both degree-zero endpoints. Its normal registered build passes in 493.733 seconds, complete recursive item/dependency kernel checking in 393.31 seconds, and all 29 new assumptions queries in 208.301 seconds. Every one of the 28,284 earlier assumption sets is preserved. The complete 28,313-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter3/3.2.md#item-3-2-45) and [validation report](checkpoints/3.2.45-product-upper-supplement-validation.json).

#### 3.2.45 — Section and product assertions

The 3.2.45-sections supplement proves the full original bounded-convex ordinary section integral, the individual anisotropic tube coefficient comparison, the all-set Gillespie upper section integral and measurable-first-factor product equality. Its normal registered build passes in 1024.389 seconds, complete recursive item/dependency kernel checking in 393.129 seconds, and all 89 new assumptions queries in 384.72 seconds. Every one of the 28,341 earlier assumption sets is preserved. The complete 28,430-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter3/3.2.md#item-3-2-45) and [validation report](checkpoints/3.2.45-sections-supplement-validation.json).

#### 3.2.45 — Sharp projection comparisons

The 3.2.45-sharp supplement proves the sharp original projection-gauge and Q_infinity <= Q_1 inequalities for every target, including degree zero and infinite masses. Its normal registered build passes in 254.586 seconds, complete recursive item/dependency kernel checking in 395.324 seconds, and all 14 new assumptions queries in 143.744 seconds. Every one of the 28,313 earlier assumption sets is preserved. The complete 28,327-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter3/3.2.md#item-3-2-45) and [validation report](checkpoints/3.2.45-sharp-supplement-validation.json).

#### 3.4.8 — Original real compact-union assertion

The 3.4.8-auxiliary supplement proves the stronger original real compact-union assertion for every A_j, B_j, C_m and E_m, with arbitrary proper ideals and both index endpoints. Its normal registered build passes in 883.463 seconds, complete recursive item/dependency kernel checking in 496.586 seconds, and all 102 new assumptions queries in 200.882 seconds. Every one of the 28,113 earlier assumption sets is preserved. The complete 28,215-entry log uses only the three permitted boolp assumptions. Inputs stayed fixed; no cleaning, adoption, copied proof objects or earlier mathematical source changes occurred. See the [item account](chapter3/3.4.md#item-3-4-8) and [validation report](checkpoints/3.4.8-auxiliary-supplement-validation.json).

## Coverage and verification recorded in the project README

The user intentionally omitted the Ward construction cited in 2.10.27.
The [omission record](checkpoints/2.10.27-ward-omission.md) preserves its
unfinished private drafts and validation limits. All three original
2.10.27 inequalities and the 2.10.29 Cantor constructions remain proved.
Chapter 1 covers §§1.2–1.10 with the qualifications in the section accounts;
§1.1.1, §1.1.2 and §1.1.4 are complete; §1.1.3 is intentionally left aside. Chapter 2
reaches the requested last proof, **2.10.48**. Sections 2.1–2.7 and 2.9
are covered as documented. §§2.8.8–2.8.9 are complete within the requested scope: subsidiary assertions
and strict-convexity uniqueness are included, and book examples are excluded.
Item 2.10.2 is complete, including actual Gamma normalization in every
nonnegative real degree and the printed circle cutoff counterexample.
The original 2.10.6 comparison and ratio assembly and the listed real-degree supplements are complete. The cited Ward construction in 2.10.27 is intentionally omitted. **2.10.46 remains partial and
deferred at the user's request.** Item 2.10.49 is a historical remark
requiring no formalisation. Chapter 2 is therefore not claimed to contain
a proof of every printed mathematical assertion.

The final compact-subset and Suslin inner-approximation results cover the
exact natural-degree Hausdorff normalisation and arbitrary nonnegative
real power gauges with explicit positive coefficients. Detailed statements,
coverage limits and proof accounts belong in the
[section documentation](toc.md).

The **release passed** the complete Chapter 2 rebuild,
full recursive kernel check and fresh audit of all 15,349 assumption queries.
The rebuild reused compatible unchanged Chapter 1 artifacts from Claude.

The [scheduled full-project validation](checkpoints/3.1-initial-full-validation.json)
completed. It passed a fresh clean rebuild of the
whole registered project, recursive kernel checking and all 15,729
assumptions queries, without warnings or changed assumption sets. Its
snapshot included the partial 3.1.4 checkpoint; later proofs receive
separate focused checks.

The [earlier full-project validation](checkpoints/3.2-checkpoint-full-validation.json)
finished: all 7,660 registered modules and 20,465
fresh assumptions queries passed. Subsequent item releases completed
1.1.2, 1.1.4, 2.8.8–2.8.9 within the requested scope, 2.10.2,
3.2.41–3.2.44 and 3.2.46–3.2.48. Each release passed registered compilation,
recursive kernel checking and a dependency assumptions audit. These
focused validations preserve all earlier assumption sets; the
3.2.48 report contains 21,855 entries. They are recorded separately
from the earlier full-project run.

[docs/verification.txt](verification.txt) records the actual scope and
outcome of every validation checkpoint. The full dependency report is
[docs/assumptions.log](assumptions.log). Only the three permitted
MathComp classical assumptions may occur: propositional extensionality,
dependent functional extensionality and constructive indefinite description.
There are no admitted proofs, new project axioms or unchecked cast bypasses.
A successful build verifies the implemented statements, not pending passages.

Chapter 3 has completed [3.1.1–3.1.24](chapter3/3.1.md), with the
conventions and qualifications documented there. The completed items passed
focused compilation, regression checks, recursive kernel checking and
assumptions audits. The commentary in 3.1.10 is recorded. The
[3.1 release](checkpoints/3.1-release-validation.json) also passed the
incremental project build, complete recursive kernel check and dependency
assumptions audit. [Subsection 3.2](chapter3/3.2.md) is complete within the stated scope: items
3.2.1–3.2.39 are complete and validated, with explicit source qualifications and
corrections in the section account. The first paragraph of 3.2.40 passed full validation; its Kneser example remains deferred. Items
3.2.41–44 and 3.2.46–48 are complete and validated. Item 3.2.45 is complete with its proved source correction, including exponent continuity, sharp comparisons, section inequalities and measurable-first-factor product equality. [Subsection 3.3](chapter3/3.3.md) is complete with the documented
source corrections and qualifications: mathematical items 3.3.1–3.3.10 and 3.3.12–3.3.21
are validated, and historical items 3.3.11 and 3.3.22 have source accounts. [Subsection 3.4](chapter3/3.4.md) has all twelve items validated through their numbered conclusions, including the Noetherian germ ring, unique factorization, corrected finite stratification, both analytic-family assertions, and the original analytic-set dimension and singular-part geometry.

Chapter 4 has not begun. Before Chapter 4, the planned
prerequisite is a formalisation of
[EilenbergSteenrod1952](bibliography.md#eilenbergsteenrod1952).

The [latest 3.3 validation](checkpoints/3.3-validation.json)
passes the incremental interface build, full `make check`, and a
dependency-aware audit refresh preserving all 23,207 previous entries.
The separate 3.3.21 release audited its 45 new declarations. Only the three
permitted boolp assumptions remain; the historical closing account adds
no theorem or assumption.

## Chapter 2 release and subsequent supplements

The release passed the Chapter 2 rebuild, full recursive
kernel check and fresh 15,349-query assumptions audit. Unchanged Chapter 1
artifacts were reused after fingerprint checks. See the
[verification record](verification.txt) and
[machine-readable release report](checkpoints/chapter2-release-validation.json).

The [clean full-project validation](checkpoints/3.2-checkpoint-full-validation.json)
finished with all 7,660 registered modules and 20,465
fresh assumptions queries passing. The Chapter 1 and 2 supplements completed
later that day have separate successful compilation, recursive kernel
checking and dependency audit records: [1.1.2](checkpoints/1.1.2-validation.json),
[1.1.4](checkpoints/1.1.4-validation.json), [2.8.8](checkpoints/2.8.8-validation.json),
[2.8.9](checkpoints/2.8.9-validation.json) and [2.10.2](checkpoints/2.10.2-validation.json).
Their coverage is included in the subsection accounts and the contents,
index, notation and divergence maps.

## Chapter 3 release accounts

[3.1 Differentials and tangents](chapter3/3.1.md), printed pp. 209–241,
is complete. Items **3.1.1–3.1.24 are completed** with their documented conventions,
zero-dimensional qualifications and erratum corrections. Their calculus,
inverse-function, Borel-measurability, partial-derivative, approximate-differential and measurable-section developments
have passed focused compilation, recursive kernel checking and assumptions
audits. The [3.1.4 completion record](checkpoints/3.1.4-validation.json)
records its final build, regression, recursive kernel check and assumptions audit.
The [3.1.5 record](checkpoints/3.1.5-validation.json) covers the subsequent
approximate-to-ordinary differentiability lemma and its punctured-center regression.
The [3.1.6 record](checkpoints/3.1.6-validation.json) covers Rademacher's
theorem, including both zero-dimensional boundaries.
The [3.1.7 record](checkpoints/3.1.7-validation.json) covers approximate
derivatives of Lipschitz maps on measurable domains.
The [3.1.8 record](checkpoints/3.1.8-validation.json) covers finite approximate
growth, the countable Lipschitz decomposition and approximate differentiability.
The [3.1.9 record](checkpoints/3.1.9-validation.json) covers Stepanoff's
theorem without a measurability premise on A.
The commentary in 3.1.10 is recorded. The [3.1.11 record](checkpoints/3.1.11-validation.json) covers higher
calculus, Taylor formulas, jets, coordinate partials and the smooth cutoff.
The [3.1.12 record](checkpoints/3.1.12-validation.json) covers the
Lipschitz-radius packing lemma, including the zero-dimensional case.
The [3.1.13 record](checkpoints/3.1.13-validation.json) covers the smooth
partition of unity on an arbitrary open cover, with its derivative bounds.
The [3.1.14 record](checkpoints/3.1.14-validation.json) covers Whitney's
extension theorem for jets of polynomials on a closed subset of R^m.
The [3.1.15 record](checkpoints/3.1.15-validation.json) covers the
approximation of maps of class k with finitely growing top differential
by maps of class k+1, up to sets of small measure.
The [3.1.16 record](checkpoints/3.1.16-validation.json) covers class-one
approximation under finite approximate growth, with an arbitrary actual domain.
The [3.1.17 record](checkpoints/3.1.17-validation.json) covers the corrected
converse, the nonmeasurable-domain and zero-source counterexamples, and
the zero-target regression.
The [3.1.18 record](checkpoints/3.1.18-validation.json) covers the complete
constant-rank normal form, its fixed smooth charts and both regressions.
The [3.1.19 record](checkpoints/3.1.19-validation.json) covers all submanifold
chart equivalences, actual coordinate homeomorphisms, local retractions,
local compactness and the isolated-point characterization.
The [3.1.20 record](checkpoints/3.1.20-validation.json) covers the full connected
submanifold/retraction equivalence and the erratum-corrected construction.
The [3.1.21 record](checkpoints/3.1.21-validation.json) covers tangent and normal
cones, transport, tangent planes, both bundles and the generic tangent-space
identities; its closing positive-reach paragraph remains a forward reference.
The [3.1.22 record](checkpoints/3.1.22-validation.json) covers relative
differentiation and class, the corrected base-value criterion, all five
submanifold differential criteria and ambient extensions.
The [3.1.23 record](checkpoints/3.1.23-validation.json) covers the complete
controlled supported straightening theorem, including the exact tangent-plane
identity and both Lipschitz bounds.
The [3.1.24 record](checkpoints/3.1.24-validation.json) covers analytic
characterizations, exact composition, general inversion and the scalar
majorant, analytic constant-rank and submanifold charts, root-set alternative
and coordinate series. The [3.1 release](checkpoints/3.1-release-validation.json)
passed its incremental all build, complete recursive kernel check and
dependency assumptions audit. [3.2 Area and coarea of Lipschitzian
maps](chapter3/3.2.md) is complete within the stated scope; items 3.2.1–3.2.39 are complete and validated,
with explicit source qualifications and corrections in the section account. The first
paragraph of 3.2.40 passed the full validation completed; only its
Kneser example remains deferred. Items 3.2.41–44 and 3.2.46–48 are complete and
validated. Item 3.2.45 is complete with its proved source correction, including its original continuity, sharp comparisons, section inequalities and product equality. [Subsection
3.3](chapter3/3.3.md) is complete with the documented source corrections and
qualifications: mathematical items 3.3.1–3.3.10 and 3.3.12–3.3.21 are validated, and
historical items 3.3.11 and 3.3.22 have source accounts. [Subsection 3.4](chapter3/3.4.md) has all twelve items validated through their numbered conclusions, including the Noetherian germ ring, unique factorization, corrected finite stratification, both analytic-family assertions, and the original analytic-set dimension and singular-part geometry.
The complex extension, including its covering and dimension corrections, is validated. The stronger original real compact-union assertion in 3.4.8(5) is proved by the [supplement](checkpoints/3.4.8-auxiliary-supplement-validation.json). The complex auxiliary analogue remains a documented limit; see the [item account](chapter3/3.4.md#item-3-4-12).
Sections 3.1–3.3 are exposed through [`Rectifiability.v`](../theories/Rectifiability.v) and tested in
[`DifferentialExamples.v`](../tests/DifferentialExamples.v) and [`InverseFunctionExamples.v`](../tests/InverseFunctionExamples.v).
Section 3.4 has separate public interfaces and compiled regression suites,
listed in its [section guide](chapter3/3.4.md).

The [3.3.1 validation](checkpoints/3.3.1-validation.json) covers all its
geometric, topological and probability assertions: 19 modules and three
regressions pass registered compilation, recursive kernel checking and
42 dependency queries. The 3.3.1 assumptions log has 21,897 entries,
with every earlier assumption set preserved. Further structure-theory
items are tracked individually in [3.3](chapter3/3.3.md).

The [3.3.2 validation](checkpoints/3.3.2-validation.json) additionally
covers the arbitrary-set Borel cone-density theorem and its published
strict-superlevel correction. Its 17 modules and three regressions pass
all stages; the 3.3.2 assumptions log has 21,931 entries.

The [3.3.3 validation](checkpoints/3.3.3-validation.json) covers
the original punctured-fibre Suslin locus: three theories and three
regressions pass registered compilation, recursive kernel checking and
10 strict dependency queries. The 3.3.3 assumptions
log has 21,941 entries, with all earlier assumption sets preserved.

The [latest 3.3 validation](checkpoints/3.3-validation.json)
passes the incremental interface build, full `make check`, and a
dependency-aware audit refresh preserving all 23,207 previous entries.
The separate 3.3.21 release audited its 45 new declarations. Only the three
permitted boolp assumptions remain; the historical closing account adds
no theorem or assumption.

Before undertaking Chapter 4, the user requests formalisation of
[EilenbergSteenrod1952](bibliography.md#eilenbergsteenrod1952). This
future prerequisite is recorded in the project plan.

### Initial releases of 3.4.7–3.4.12

#### 3.4.7

Federer 3.4.7 is complete and validated: both null exceptional-direction
sets, the actual finite-dimensional Noetherian germ ring, and unique
factorization at every centre. All 161 new theories and the three actual
regressions pass registered compilation (241.71s), complete recursive
item-and-dependency kernel checking (164.97s), and all 635 new strict
assumptions queries (148.53s). All 24,395 earlier results are preserved;
the complete log has 25,030 entries and only the three permitted boolp
assumptions. See the [item account](chapter3/3.4.md#item-3-4-7) and
[validation report](checkpoints/3.4.7-validation.json).

At that checkpoint, items 3.4.8–3.4.12 remained. The final full-project rebuild, check and audit subsequently passed,
with the run starting after 17:00 Europe/Warsaw. The preserved README and section-release accounts
below describe the earlier state through 3.4.6.

#### 3.4.8

The numbered conclusions of Federer 3.4.8 pass registered compilation,
complete recursive item/dependency kernel checking and strict dependency
audit. The compact-component obligation of 3.4.5 is discharged. At this initial release, the stronger sigma-compactness sentence in
the printed proof of (5) was unproved. Its real case now has the
[compact-union supplement](checkpoints/3.4.8-auxiliary-supplement-validation.json);
the numbered Borel conclusion retains its independent complete proof.
See the [item account](chapter3/3.4.md#item-3-4-8) and
[validation report](checkpoints/3.4.8-validation.json).

#### 3.4.9

Both original assertions of 3.4.9 pass registered compilation, complete
recursive item/dependency kernel checking and strict dependency audit.
See the [item account](chapter3/3.4.md#item-3-4-9) and
[validation report](checkpoints/3.4.9-validation.json).

#### 3.4.10

Every original assertion of 3.4.10 passes registered compilation, complete
recursive item/dependency kernel checking and strict dependency audit.
See the [item account](chapter3/3.4.md#item-3-4-10) and
[validation report](checkpoints/3.4.10-validation.json).

#### 3.4.11

Every original assertion of 3.4.11 passes registered compilation, complete
recursive item/dependency kernel checking and strict dependency audit.
See the [item account](chapter3/3.4.md#item-3-4-11) and
[validation report](checkpoints/3.4.11-validation.json).

<a id="latest-numbered-item-release"></a>

#### 3.4.12

The original complex extension in 3.4.12 passes registered compilation,
complete recursive item/dependency checking, and all new strict assumptions
queries. All numbered assertions of 3.4 are now validated, with the source
corrections and auxiliary proof limit recorded in the section guide.
See the [item account](chapter3/3.4.md#item-3-4-12) and
[validation report](checkpoints/3.4.12-validation.json).
The full-project validation reported above subsequently passed.

## Individual release records

The [full-project validation](checkpoints/3.2-checkpoint-full-validation.json) completed: all 7,660 registered modules rebuilt cleanly, complete recursive kernel checking and all 20,465 fresh assumption queries passed without warnings; all 20,393 earlier assumption sets were preserved. This does not extend coverage to unregistered drafts.

Federer 1.1.2 is complete and validated, including arbitrary finite-family canonical maps and product bases. See [the item record](checkpoints/1.1.2-validation.json).

Federer 1.1.4 is complete and validated, including unrestricted injectivity and the exact finite-factor surjectivity criterion. See [the item record](checkpoints/1.1.4-validation.json).

Federer 2.8.8 is complete and validated within the requested scope, including subsidiary assertions and excluding the book examples. See [the item record](checkpoints/2.8.8-validation.json).

Federer 2.8.9 is complete and validated within the requested scope, including strict-convexity and actual inner-product radial uniqueness. See [the item record](checkpoints/2.8.9-validation.json).

Federer 2.10.2 is complete and validated, including real dimensions and the circle example. See [the item record](checkpoints/2.10.2-validation.json).

Federer 3.2.41 is complete and validated with the scope and qualifications in [its record](checkpoints/3.2.41-validation.json).

Federer 3.2.42 is complete and validated with the scope and qualifications in [its record](checkpoints/3.2.42-validation.json).

Federer 3.2.43 is complete and validated with the scope and qualifications in [its record](checkpoints/3.2.43-validation.json).

Federer 3.2.44 is complete and validated with the scope and qualifications in [its record](checkpoints/3.2.44-validation.json).

Federer 3.2.46 is complete and validated in the single-chart scope, with the disconnected-domain qualification in [its record](checkpoints/3.2.46-validation.json).

## Documentation audit

The [documentation reorganisation record](checkpoints/documentation-reorganisation.json)
records preservation checks, link checks, HTML rendering, and the revision
of the error catalogue. This documentation work changes no proof source
and provides no new mathematical validation.

The [documentation audit](checkpoints/documentation-audit.json)
checks current coverage, local source links, historical checkpoint labels and
the error-list proof references against the validated formalisation.

The [checkpoint catalogue](checkpoints/README.md) lists the historical records.
The complete chronological build record remains in [verification.txt](verification.txt).
