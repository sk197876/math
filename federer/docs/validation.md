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

## Proof development aids

[Rocqet](https://github.com/LLM4Rocq/rocqet-search) provides a local semantic
index of the audited public library. Search returns declaration names,
source lines, statements and the existing book comments. The index admits
only committed registered sources whose compiler metadata matches their
contents. Its manifest records ambiguous names and generated declarations
without usable source offsets. These entries are omitted from search.
The embedding model and vector store remain on the local machine.

On the shared development host, query it with:

```sh
/opt/rocq/federer-build/tooling/rocqet/search --limit 8 "compact current extension"
```

Refresh the index after a release has passed validation and been committed:

```sh
/opt/rocq/federer-build/tooling/rocqet/refresh
```

The refresh reuses unchanged vectors. Both commands follow the automatic
[resource policy](resources.md); during the day they also exclude concurrent
compiler work and active registered validation. Search results guide library
navigation. Read the actual public statement and check its application in
Rocq. A search result does not override the restrictions on construction
modules or certify a new proof.

[Rocq MCP](https://github.com/LLM4Rocq/rocq-mcp) supports live goal inspection,
library queries and tactic trials. The project uses an isolated draft tree,
the pinned compiler switch and the shared compiler lock. Successful
interactive proofs receive ordinary full compilation. Before registered
validation, close the interactive session, archive its scratch tree and
remove its private load-path overlay. Register plaintext sources; retain
private proof objects only as historical evidence.

The [MathComp skill](https://github.com/LLM4Rocq/mathcomp-skills) supplies
search and proof-development guidance. Its workflow is to inspect the goal,
search existing results, test a few tactics without advancing the state,
and commit the successful tactic. The project's earlier requirements for
book fidelity, self-containment, axiomatic specifications, opaque interfaces,
source comments and proof integrity govern this use. Every numbered release
still needs registered compilation, its complete recursive consumer kernel
check and the strict dependency audit.

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

Chapter 4 is in progress through the validated items 4.1.1–4.1.27.
Items 4.1.28–4.1.34 remain pending.
The planned prerequisite for its later homology theory is a formalisation
of [EilenbergSteenrod1952](bibliography.md#eilenbergsteenrod1952).

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

Formalisation of [EilenbergSteenrod1952](bibliography.md#eilenbergsteenrod1952)
remains a prerequisite for later homology results in Chapter 4.

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

## Chapter 4 release accounts

### 4.1.1 — Test functions and distributions

All 232 new theories and the example suite pass normal registered
compilation in 996.175s. Complete recursive consumer checking passes in
280.879s. The 292 new strict assumptions queries pass in 398.919s;
every one of the 28,430 earlier assumption sets is preserved, and the
complete log contains 28,722 entries with only the three permitted
boolp assumptions. No earlier mathematical proof source changed.

The release preserves Federer's final test topology and proves its
comparison with the locally convex topology for the actual test space.
The nonembedding theorem includes the missing nonzero-source hypothesis,
with an actual zero-dimensional Banach counterexample. Empty domains,
derivative degree zero and a distribution with noncompact support have
checked regressions. The precise coverage and qualified source prose are
in the [item account](chapter4/4.1.md#item-4-1-1).

Validation reused unchanged registered dependencies. Four compiler workers,
nice 10, the required switch, group llm and group write access were used;
compilation, kernel checking and the audit ran in sequence. No private proof
object was copied or adopted. Later 4.1 items remain pending. See the
[validation report](checkpoints/4.1.1-validation.json).

### 4.1.2 — Regularisation

All 166 new theories and the example suite pass normal registered
compilation in 962.766s. The complete recursive consumer closure passes kernel
checking in 324.557s. All 255 new strict assumptions queries pass in 560.648s;
all 28,722 earlier assumption sets are preserved. The complete log has
28,977 entries and only the three permitted boolp assumptions.

The release includes every original Lebesgue point, full input differentials,
the locally Lipschitz/reflexive clause with its original partial derivative
domain, actual norm-smooth distribution densities, finite partition
interchange, and joint weak approximation on arbitrary open sets. Test
limits use one compact step in the literal final topology. The boundary
suite checks dimension zero, scale one, zero input and an empty domain.
All stages used the required switch, nice 10, group llm and group read/write.
No earlier mathematical proof source changed; no private proof object was
copied or adopted. See the [validation report](checkpoints/4.1.2-validation.json)
and [query log](checkpoints/4.1.2-assumptions.log).

### 4.1.3 — Tensor density

All 41 new theories and the two-case boundary suite pass normal registered
compilation in 320.654s and complete recursive kernel checking in 288.288s.
All 49 new strict assumptions queries pass in 168.175s; all 28,977 earlier
assumption sets are preserved. The complete log has 29,026 entries and
only the three permitted boolp assumptions.

The original canonical map is opaque and satisfies the coordinate-product
law. An actual common scalar factor supplies the normalized product
kernel. The book's finite Borel sums lie in its image and approach every
test in the literal final topology. Continuous-range adapters retain
arbitrary Banach targets, including nonseparable targets. Dimension zero
has two checked regressions. No earlier proof source changed; no private
proof object was copied or adopted. See the
[validation report](checkpoints/4.1.3-validation.json) and
[query log](checkpoints/4.1.3-assumptions.log).

### 4.1.4 — Distribution constancy

All 45 new theories and the three-case boundary suite pass normal registered
compilation in 356.313s and complete recursive kernel checking in 301.917s.
All 76 new strict assumptions queries pass in 147.746s; all 29,026 earlier
assumption sets are preserved. The complete log has 29,102 entries and
only the three permitted boolp assumptions.

The theorem retains the original coordinate derivative-support hypothesis,
arbitrary open U, connected open A, every original supported test and the
literal integral over U. Original inner components capture compact supports;
the actual norm-smooth density is constant there, and Federer's fixed unit
kernel test identifies the constants. The proved cutoff and zero-extension
laws give the original open-domain reduction. Empty A, dimension zero and
an empty complement have checked actual-space regressions. No earlier
proof source changed; no private proof object was copied or adopted.
See the [validation report](checkpoints/4.1.4-validation.json) and
[query log](checkpoints/4.1.4-assumptions.log).

### 4.1.5 — Representation by integration

All 132 new theories and the four-case actual-space boundary suite pass
normal registered compilation in 1039.038s and complete recursive consumer
kernel checking in 319.751s. All 260 new strict assumptions queries pass in
314.314s, preserving all 29,102 earlier assumption sets. The complete log has
29,362 entries and only the three permitted boolp assumptions.

The release retains the original compact scalar-test gauge, proves the full
finite-gauge criterion and the original convolution extension with its
sharp bound, and identifies the gauge with its Radon variation. The actual
weak dual density has norm one almost everywhere. Original tests are dense
in the whole partial-domain L1 space; its opaque integral extension is
linear, almost invariant, one-Lipschitz and unique. One conull set gives the
original characteristic-ball quotient for every target vector. The exact
scalar Daniell variation, both weak lower-limit inequalities and original
monotone-bound weak compactness are proved. M need not be homogeneous.
No earlier proof source changed; no private proof object was copied or
adopted. See the [validation report](checkpoints/4.1.5-validation.json) and
[query log](checkpoints/4.1.5-assumptions.log).

### 4.1.6 — Differential forms

All 82 new theories and the five-case boundary suite pass ordinary registered
compilation in 1215.066s, complete recursive consumer kernel checking in 198.078s,
and all 227 new strict queries in 221.749s. Every one of the 29,362 earlier
assumption sets is preserved. The complete log has 29,589 entries and
only the three permitted boolp assumptions.

The release includes the original fields and coordinate expansions,
induced multilinear norm, exterior derivative, graded product rule,
square zero, divergence, duality and full pullback commutation. The partial
domains and literal twice differentiability are retained for every normed
coefficient space, without whole-target completeness or separability.
The actual zero-dimensional and empty-domain regressions pass. One build
worker was used; the registered stages ran in sequence. Historical private
queue failures remain excluded; all affected modules passed sequential
rechecks before registration. No earlier proof source changed, and no
private proof object was copied or adopted. See the
[validation report](checkpoints/4.1.6-validation.json) and
[query log](checkpoints/4.1.6-assumptions.log).

### 4.1.7 — Currents, mass and proper pushforward

All 382 new theories and three actual-space example sources pass ordinary
registered compilation in 3633.684s and complete recursive consumer
kernel checking in 531.426s. All 916 new strict queries pass in
3131.941s. Every one of the 29,589 earlier assumption sets is preserved;
the complete log has 30,505 entries and only the three permitted boolp
assumptions. Two build workers were used. The registered stages ran in
sequence, with no private compiler alongside the build or kernel check.
No earlier mathematical proof source changed, and no private proof object
was copied or adopted. See the [validation report](checkpoints/4.1.7-validation.json)
and [query log](checkpoints/4.1.7-assumptions.log).

The first audit stopped after 708 results because query registration
included an implementation helper hidden by a sealed module. Its
public measure, density and laws, and the independent existence
theorem, remain queried. No proof, module signature or allowed
assumption changed. The failed run and its partial log are retained
and excluded. All 916 public names then passed an ordinary Rocq
preflight in 25.182s. The cached
build reconfirmation passed in 28.858s without
recompiling mathematical sources; the complete kernel check and
strict audit were repeated on the corrected registration.

The release covers all original assertions on pp. 355–359, with
the corrected uniqueness qualification in the actual half-line example.
The exact orientation domain, all-set variation, both local normality
criteria, original class-one boundary action and support-proper
pushforward retain their printed scope. The empty-domain and
zero-dimensional regressions pass. The kernel check includes the
complete recursive dependencies of Currents and all three example
consumers. The strict audit selects only the 916 new fully qualified
queries; their complete dependencies are loaded normally.

### 4.1.8 — Cartesian products of currents

The 249 new theories and the example file with three $\mathbf R^0$ regressions passed
ordinary registered compilation in 2627.274s, complete recursive consumer
kernel checking in 627.662s and all 483 new strict queries in 1760.478s.
All 30,505 earlier assumption sets are preserved. The complete log has
30,988 entries and only the three permitted boolp assumptions. See the
[report](checkpoints/4.1.8-validation.json) and
[new-query log](checkpoints/4.1.8-assumptions.log). The kernel check covers
CartesianCurrents and the endpoint example with their complete recursive
dependencies. An ordinary Rocq name preflight confirms all 483 public
queries. No earlier mathematical proof source changed; no private proof
object was copied or adopted. A cached build reconfirmation after the
documentation index update passed in 29.867s. All registered stages used
the automatic day/night resource policy, the required switch, nice 10,
umask 0002, group llm and group read/write.

The scope includes every in-book mathematical paragraph on pp. 360–362:
arbitrary-current products and all mixed degrees, exact support, all three
boundary cases, algebraic identities and compact projection; the original
Radon density, both variation comparisons and equality when either orientation is simple;
segments, point products, finite Stokes and the exact ordered scalar-box
restriction. See the [item account](chapter4/4.1.md#item-4-1-8).

### 4.1.9 — Homotopy formulas and affine mass estimates

The 108 new theories and one endpoint example source passed ordinary
registered compilation in 578.036s, complete recursive consumer kernel
checking in 492.798s and all 274 new strict dependency queries in
1489.859s. All 30,988 earlier assumption sets are preserved. The complete
log has 31,262 entries and only the three permitted boolp assumptions.
See the [validation report](checkpoints/4.1.9-validation.json) and
[new-query log](checkpoints/4.1.9-assumptions.log). An ordinary Rocq
preflight confirms every public query name. No earlier mathematical proof
source changed; no private proof object was copied or adopted. The stages
ran in sequence under the automatic day/night resource policy, with the
required switch, nice 10, umask 0002, group llm and group read/write. The OOM killer and the live interactive-reserve guard stopped the 3 earlier build attempts; 43 sources had compiled normally. The new registered files used a smaller ordinary Rocq-generated build graph; canonical make all then confirmed the complete active tree. The daytime attempts retained their safeguards and reused only ordinary registered objects. The remaining files and validation stages completed under the permitted night policy. The failed attempts remain retained and excluded; the report gives every duration.

The release covers every original mathematical assertion on pp. 363–364.
The current identities require only properness on the closed time cylinder
over the actual support. Both original test restatements and both pointwise
form identities pass. The represented-current clause retains its exact
partial orientation weight and sharp all-set variation comparison. All three
affine estimates include the printed coefficient, degree zero and infinite
masses. The actual stationary nonzero zero-current and scalar endpoint
regressions pass. See the [item account](chapter4/4.1.md#item-4-1-9).

### 4.1.10 — Cone primitives and star-shaped domains

The 21 new theories and one endpoint example source passed ordinary
registered compilation in 263.686s, complete recursive consumer kernel
checking in 448.210s and all 59 new strict dependency queries in 329.405s.
All 31,262 earlier assumption results are preserved. The complete log has
31,321 entries and only the three permitted boolp assumptions. An ordinary
Rocq preflight confirms all 59 public names. See the
[validation report](checkpoints/4.1.10-validation.json) and
[new-query log](checkpoints/4.1.10-assumptions.log). No earlier
mathematical proof source changed; no private proof object was copied or
adopted. The stages ran in sequence under the automatic day/night policy,
with the required switch, nice 10, umask 0002, group llm and group read/write.

The release covers every original mathematical assertion on p. 364. It
applies the published compact-test superscript correction and retains the
literal primitive integral, both compact-current endpoint actions, all three
current conclusions and every original star-shaped open domain. The cone
has the exact compact segment support. The actual nonzero dimension-zero
point-current regressions pass. See the [item account](chapter4/4.1.md#item-4-1-10).

### 4.1.11 — Joins and oriented simplexes

The 229 new theories and one source with four endpoint regressions passed
ordinary registered compilation in 1986.599s, complete recursive
consumer kernel checking in 524.178s and all 608 new strict
dependency queries in 3319.871s. All 31,321 earlier assumption
results are preserved. The complete log has 31,929 entries and only the
three permitted boolp assumptions. An ordinary Rocq preflight confirms all
608 public names. See the [validation report](checkpoints/4.1.11-validation.json)
and [new-query log](checkpoints/4.1.11-assumptions.log). No earlier
mathematical proof source changed; no private proof object was copied or
adopted. The stages ran in sequence under the automatic day/night policy,
with the required switch, nice 10, umask 0002, group llm and group read/write.

The release covers every original assertion on pp. 364–366. The algebraic
laws retain arbitrary compact currents. The mass assertions retain their
original representation hypotheses, partial orientations and exact integral
coefficient. The simplex, prism and rectangular formulas include degenerate
vertices and dimension zero. Associativity follows the printed triangle
proof. All four actual-space endpoint regressions pass. See the
[item account](chapter4/4.1.md#item-4-1-11). Failed private checks remain
retained and excluded; their objects were never adopted.

### 4.1.12 — Flat seminorms and flat chains

The 169 new theories and 1 endpoint source passed
ordinary registered compilation in 1269.299s, complete recursive
consumer kernel checking in 773.056s and all 376 new
strict dependency queries in 1761.823s. All 31,929 earlier
assumption results are preserved. The complete log has 32,305
entries and only the three permitted boolp assumptions. An ordinary Rocq
preflight confirms all 376 public query names. See the
[validation report](checkpoints/4.1.12-validation.json) and
[new-query log](checkpoints/4.1.12-assumptions.log). No earlier
mathematical proof source changed; no private proof object was copied or
adopted. The stages used the required switch, nice 10, umask 0002, group llm
and group read/write under the automatic resource policy.

The release covers every original in-book mathematical assertion on
pp. 367–369. The attained mass minimum includes infinite values. Boundary,
scalar, local and Cartesian laws retain their original support and
partial-operation domains. The original dyadic and weighted interval
counterexamples are proved, including exact mass, support and test formulas.
The finite-mass nonflat example anticipated in this item is now proved
in [4.1.15](chapter4/4.1.md#item-4-1-15).
The four assertions for the actual nonzero dimension-zero point current
pass. See the [item account](chapter4/4.1.md#item-4-1-12). No new mathematical
source error was found. Failed private checks remain retained and excluded;
their objects were never adopted.

### 4.1.13 — Flat estimates for smooth images

The 27 new theories and 1 endpoint source passed
ordinary registered compilation in 293.216s, complete recursive
consumer kernel checking in 834.169s and all 80 new
strict dependency queries in 198.938s. All 32,305 earlier
assumption results are preserved. The complete log has 32,385
entries and only the three permitted boolp assumptions. An ordinary Rocq
preflight confirms all 80 public query names. See the
[validation report](checkpoints/4.1.13-validation.json) and
[new-query log](checkpoints/4.1.13-assumptions.log). No earlier
mathematical proof source changed; no private proof object was copied or
adopted. The stages used the required switch, nice 10, umask 0002, group llm
and group read/write under the automatic resource policy.

The release covers the original proposition and its proof on pp. 369–370.
The compact C is exactly the original segment union over the support.
Both degree cases retain the original maps, actual differentials, variation
measures and integral values, with coefficient one and no extra
integrability premise. The six actual-space endpoint assertions exercise
the final public theorems, including empty source and target and a
nonconvex target for which whole-source affine containment fails. See the
[item account](chapter4/4.1.md#item-4-1-13). No new mathematical source error
was found. Failed private checks remain retained and excluded; their
objects were never adopted.

### 4.1.14 — Lipschitz images of flat currents

The 212 new theories and 3 endpoint sources passed
ordinary registered compilation in 1722.896s, complete recursive
consumer kernel checking in 826.483s and all 436 new
strict dependency queries in 1574.056s. All 32,385 earlier
assumption results are preserved. The complete log has 32,821
entries and only the three permitted boolp assumptions. An ordinary Rocq
preflight confirms all 436 public query names. See the
[validation report](checkpoints/4.1.14-validation.json) and
[new-query log](checkpoints/4.1.14-assumptions.log). No earlier
mathematical proof source changed; no private proof object was copied or
adopted. The stages used the required switch, nice 10, umask 0002, group llm
and group read/write under the automatic resource policy.

The release covers every original mathematical assertion of 4.1.14 on
pp. 370–372. The compact definition retains every allowed source
representative and smooth family, with differential bounds only on K.
The actual proper local operator preserves linearity, support, boundary,
composition and both original closed-cylinder homotopy formulas. Weighted
bounds keep the continuous Lebesgue-almost-everywhere differential premise,
original source variation and support-only affine-image condition. The
class-one law permits every continuous target form. Actual-space endpoint
regressions include empty opens and compact indices, zero currents, the
nonzero degree-zero constant image, a vanishing positive-degree constant
image, identity on a nonzero interval, and the actual unit affine chain
with sigma zero and degree zero. See the
[item account](chapter4/4.1.md#item-4-1-14). No new mathematical source error
was found. Failed private checks remain retained and excluded; their
objects were never adopted.

### 4.1.15 — Support coincidence and flat-current supports

The 55 new theories and 1 endpoint source passed
ordinary registered compilation in 463.777s, complete recursive
consumer kernel checking in 531.310s and all 139 new
strict dependency queries in 333.725s. All 32,821 earlier
assumption results are preserved. The complete log has 32,960
entries and only the three permitted boolp assumptions. An ordinary Rocq
preflight confirms all 139 public query names. See the
[validation report](checkpoints/4.1.15-validation.json) and
[new-query log](checkpoints/4.1.15-assumptions.log). No earlier
mathematical proof source changed; no private proof object was copied or
adopted. The stages used the required switch, nice 10, umask 0002, group llm
and group read/write under the automatic resource policy.

The release covers every original mathematical assertion of 4.1.15 on
pp. 372–373. The radial construction and actual common-kernel smoothing
prove support coincidence for the original locally Lipschitz maps and
every compact flat current, without an equality premise on its compact
index. Retraction locality, both point-support formulas, all three
section-image sets and the arbitrary affine-plane obstruction retain
their original hypotheses. The actual compact point one-current has
mass one and infinite boundary mass and is not flat. Genuine compact
smooth tests tend uniformly to zero with bounded differentials, while
their current images and pushed boundaries fail to converge. The
degree-one target corrects the final sentence on p. 373. See the
[item account](chapter4/4.1.md#item-4-1-15) and the
[error catalogue](references/federer-errors.tex). Failed private checks
remain retained and excluded; their objects were never adopted.

### 4.1.16 — Convex retractions and flat norms

The 12 new theories and 1 endpoint source passed
ordinary registered compilation in 183.976s, complete recursive
consumer kernel checking in 562.658s and all 41 new
strict dependency queries in 123.025s. All 32,960 earlier
assumption results are preserved. The complete log has 33,001
entries and only the three permitted boolp assumptions. An ordinary Rocq
preflight confirms all 41 public query names. See the
[validation report](checkpoints/4.1.16-validation.json) and
[new-query log](checkpoints/4.1.16-assumptions.log). No earlier
mathematical proof source changed; no private proof object was copied or
adopted. The stages used the required switch, nice 10, umask 0002, group llm
and group read/write under the automatic resource policy.

The release covers every original mathematical assertion of 4.1.16 on
pp. 373–374. The independent nearest-point graph and opaque map apply
to arbitrary nonempty closed convex sets, including unbounded sets.
The literal segment square, minimum, two variational inequalities and
pair inequality give the original Lipschitz bound one. Each flat
current lies in the compact flat space indexed by the exact convex
hull of its support. Its flat norm there equals its flat norm at every
larger compact index. Empty support is treated before choosing a
nearest-point map, and degree zero and zero ambient dimension remain
included. The published ambient-space correction is recorded in the
[error catalogue](references/federer-errors.tex); no new source error
was found. See the [item account](chapter4/4.1.md#item-4-1-16). Failed
private checks remain retained and excluded; their objects were never
adopted.

### 4.1.17 — Mass approximation and summable contractions

The 11 new theories and 1 endpoint source passed
ordinary registered compilation in 214.530s, complete recursive
consumer kernel checking in 537.327s and all 28 new
strict dependency queries in 118.255s. All 33,001 earlier
assumption results are preserved. The complete log has 33,029
entries and only the three permitted boolp assumptions. An ordinary Rocq
preflight confirms all 28 public query names. See the
[validation report](checkpoints/4.1.17-validation.json) and
[new-query log](checkpoints/4.1.17-assumptions.log). No earlier
mathematical proof source changed; no private proof object was copied or
adopted. The stages used the required switch, nice 10, umask 0002, group llm
and group read/write under the automatic resource policy.

The release covers both original mathematical paragraphs of 4.1.17 on
p. 374. The exact normal mass-closure equality derives support and
finite mass on its closure side and retains the original compact
index. Its normal approximant is the published correction
$Q+\partial S$. Smooth contraction, actual test-product bounds and
variation $L^1$ density prove the contraction assertion for every
original summable form. The final wrapper derives representation and
local summability; it adds no boundedness, smoothness or compact
support to the coefficient. The separate density law preserves
conull partial domains. Both zero-degree endpoints, empty domains
and compact indices, and zero ambient dimension remain. The actual
point regressions check both the singleton and empty index. No new
source error was found. See the
[item account](chapter4/4.1.md#item-4-1-17) and
[error catalogue](references/federer-errors.tex). Failed private
checks remain retained and excluded; their objects were never adopted.

### 4.1.18 — Smoothing and compact L1 representations

The 220 new theories and 1 endpoint source passed
ordinary registered compilation in 2085.343s, complete recursive
consumer kernel checking in 719.550s and all 480 new
strict dependency queries in 1055.693s. All 33,029 earlier
assumption results are preserved. The complete log has 33,509
entries and only the three permitted boolp assumptions. An ordinary Rocq
preflight confirms all 480 public query names. See the
[validation report](checkpoints/4.1.18-validation.json) and
[new-query log](checkpoints/4.1.18-assumptions.log). No earlier
mathematical proof source changed; no private proof object was copied or
adopted. The stages used the required switch, nice 10, umask 0002, group llm
and group read/write under the automatic resource policy.

The release covers every original mathematical assertion of 4.1.18 on
pp. 374–377. Arbitrary-current smoothing retains the reflected translation
average, actual deformation current, all degree cases and sharp mass,
support and flat-error bounds, including infinite masses. The actual
averaged translated Radon variation bounds every set; its compact
majorants give weak variation convergence for arbitrary represented
currents. The corresponding original form homotopies are included.

For every open U, both compact L1 pair propositions retain their exact
flat indices, radius-delta supports and cost bounds. The proof includes
the original normal approximation, residual iteration, both infinite
sums on the common half-radius compact carrier, and downward degree
induction. The original flat current need not have finite mass or be
normal. The opaque onto map, quotient fibres, top-degree characterization
and both directions of the literal J-kernel closure are proved. The raw
field cost is a seminorm under almost equality; this carrier convention
is not a new source error. Actual nonzero R0 point regressions and the
general empty and degree endpoints are included. See the
[item account](chapter4/4.1.md#item-4-1-18) and
[error catalogue](references/federer-errors.tex). Failed private checks
remain retained and excluded; their objects were never adopted.

### 4.1.19 — Flat cochains and measurable forms

The 105 new theories passed ordinary registered
compilation in 964.030s, complete recursive consumer kernel checking
in 652.887s and all 207 new strict dependency queries in
516.855s. All 33,509 earlier assumption results are
preserved. The complete log has 33,716 entries and only the three
permitted boolp assumptions. An ordinary Rocq preflight confirms all
207 public query names. See the
[validation report](checkpoints/4.1.19-validation.json) and
[new-query log](checkpoints/4.1.19-assumptions.log). The complete
consumer closure includes the facade, both actual null-spike counterexamples
and the original open-domain L1 duality. No earlier mathematical proof source
changed; no private proof object was copied or adopted. The stages used the
required switch, nice 10, umask 0002, group llm and group read/write under the
automatic resource policy.

The release covers all twelve original mathematical groups of 4.1.19 on
p. 377. The source continuation on p. 378 is historical commentary.
Cochains use the actual flat-current union and one finite bound for every
compact index. The least nonnegative norm, actual coboundary, signed unit
pair-ball supremum, both bounded measurable actions, almost uniqueness,
weak equation, converse and coboundary pair are included.

The norm formula for arbitrary representatives uses essential comass.
Selected representatives retain the literal global-comass formula on
nonempty U, with an explicit all-domain zero-threshold version. The
class-one criterion is almost equality for measurable second forms and
pointwise equality for continuous ones. The actual zero-cochain and smooth
zero-first-form null spikes prove the two local representative corrections.
Smoothing equivalence uses every positive radius on its original valid
interior locus and actual smooth convolution families. Empty domains,
zero ambient dimension and above-dimensional degrees are included.
The five final consumer roots recursively cover every new source, including
the original open-domain L1 duality. See the
[item account](chapter4/4.1.md#item-4-1-19) and
[error catalogue](references/federer-errors.tex). Failed private checks
remain retained and excluded; their objects were never adopted.

### 4.1.20 — Integral-geometric null support

The 17 new theories passed ordinary registered compilation in
283.433s, complete recursive consumer kernel checking in
670.183s and all 22 new strict dependency queries in
140.098s. All 33,716 earlier assumption results are
preserved. The complete log has 33,738 entries and only the three
permitted boolp assumptions. An ordinary Rocq preflight confirms every new
public query name. See the [validation report](checkpoints/4.1.20-validation.json)
and [new-query log](checkpoints/4.1.20-assumptions.log).
The complete consumer root covers every new source. No earlier mathematical
proof source changed; no private proof object was copied or adopted.
The stages used the required switch, nice 10, umask 0002, group llm and
group read/write under the automatic resource policy.

The release covers the entire original theorem and its printed proof on
p. 378. The support-null hypothesis uses the original I_1^m measure. The
orthogonal choice, finite coordinate expansion, compact scalar contractions,
projected top-degree vanishing and exact inverse/open-domain recovery are
included. No normality, finite-mass, measurable-support or representation
premise is added. Positive degree and the original measure's ambient-index
qualification remain explicit. No new source correction is claimed. See
the [item account](chapter4/4.1.md#item-4-1-20). Failed private checks remain
retained and excluded; their objects were never adopted.

### 4.1.21 — Null-set corollaries for flat currents

The 7 new theories and 1 example
source passed ordinary registered compilation in
171.442s, complete recursive consumer kernel checking in
690.280s and all 13 new strict dependency queries in
144.533s. All 33,738 earlier assumption results are
preserved. The complete log has 33,751 entries and only the three
permitted boolp assumptions. An ordinary Rocq preflight confirms every new
public query name. See the [validation report](checkpoints/4.1.21-validation.json)
and [new-query log](checkpoints/4.1.21-assumptions.log).
The complete consumer root covers every new source. No earlier mathematical
proof source changed; no private proof object was copied or adopted.
The stages used the required switch, nice 10, umask 0002, group llm and
group read/write under the automatic resource policy.

The release covers both original corollaries on p. 378. The first keeps
arbitrary B and only the printed relative closedness of support minus B;
it adds no finite-mass or representation premise. The second keeps
arbitrary E, deriving representation and finite Radon variation from
finite current mass. The Borel-null-hull reduction, compact measurable
flat restriction, exact support, variation and mass laws, above-dimension
consequences and three actual endpoint regressions are included. No new
source correction is claimed. See the
[item account](chapter4/4.1.md#item-4-1-21). Failed private checks remain
retained and excluded; their objects were never adopted.

### 4.1.22 — Integral and real polyhedral chains

The 25 new theories and 1 example
source passed ordinary registered compilation in
284.171s, complete recursive consumer kernel checking in
872.916s and all 167 new strict dependency queries in
552.397s. All 33,751 earlier assumption results are
preserved. The complete log has 33,918 entries and only the three
permitted boolp assumptions. An ordinary Rocq preflight confirms every new
public query name. See the [validation report](checkpoints/4.1.22-validation.json)
and [new-query log](checkpoints/4.1.22-assumptions.log).
The complete consumer root covers every new source. No earlier mathematical
proof source changed; no private proof object was copied or adopted.
The stages used the required switch, nice 10, umask 0002, group llm and
group read/write under the automatic resource policy.

The release covers all four definitions and their asserted algebraic
structures on p. 379: the integral subgroup for each original compact K,
its real algebraic span, and both full compact unions. Opaque carriers
have injective public inclusions with exactly those current images.
The existing simplex currents supply the generators. Support, normality,
flatness, boundary and same-index open restriction are included as earlier
prerequisites for the following items. Empty indices, empty opens,
above-dimensional currents and nonzero signed degree-zero points remain
covered. No new source correction is claimed. See the
[item account](chapter4/4.1.md#item-4-1-22). Failed private checks remain
retained and excluded; their objects were never adopted.

### 4.1.23 — Polyhedral approximation

The 76 new theories and 1 example
source passed ordinary registered compilation in
989.500s, complete recursive consumer kernel checking in
1203.591s and all 134 new strict dependency queries in
410.392s. All 33,918 earlier assumption results are
preserved. The complete log has 34,052 entries and only the three
permitted boolp assumptions. An ordinary Rocq preflight confirms every new
public query name. See the [validation report](checkpoints/4.1.23-validation.json)
and [new-query log](checkpoints/4.1.23-assumptions.log).
The complete consumer roots cover every new source. No earlier mathematical
proof source changed; no private proof object was copied or adopted.
The stages used the required switch, nice 10, umask 0002, group llm and
group read/write under the automatic resource policy.

The release covers the original theorem and all five printed reductions
on pp. 379–380. The given compact K lies in the interior of C, while C
may be nonconvex. The final real polyhedral current keeps the compact
flat error and mass error, including infinite input mass. The full
rectangular product and transverse atomic argument retain exact mass,
nonempty tags, the printed cone error and every generator hull. Empty
indices, signed degree-zero terms, zero-volume pieces and the transverse
one-point space in top degree remain covered. The later normal-mass
strengthening belongs to 4.2.24. No new source correction is claimed. See
the [item account](chapter4/4.1.md#item-4-1-23). Failed private attempts
remain retained and excluded; their proof objects were never adopted.

### 4.1.24 — Rectifiable currents, integral currents and integral flat chains

The 77 new theories and 1 example
source passed ordinary registered compilation in
3832.446s, complete recursive consumer kernel checking in
991.046s and all 220 new strict dependency queries in
9540.479s. All 34,052 earlier assumption results are
preserved. The complete log has 34,272 entries and only the three
permitted boolp assumptions. An ordinary Rocq preflight confirms every new
public query name. See the [validation report](checkpoints/4.1.24-validation.json)
and [new-query log](checkpoints/4.1.24-assumptions.log).
The consumer root `FedererTests.IntegralCurrentEndpointExamples` reaches
every new source. No earlier mathematical proof source changed; no private
proof object was copied or adopted. The stages used the required switch,
nice 10, umask 0002, group llm and group read/write under the automatic
resource policy. Two earlier registered builds were stopped through the
resource guard when the daytime policy changed; they are retained and
not promoted.

The release covers the definitions and assertions on pp. 380–382: the
three integer classes for each compact K, their global and local unions,
every inclusion of the diagram on p. 381, the equality of rectifiable and
integral polyhedral zero-currents, Lipschitz images, the integral flat
size and its metric, both density and both completeness assertions with
the series estimate, the finite-mass decomposition of flat chains and the
attained flat filling. Finite mass, support and flatness are derived from
the approximation definition. Empty indices, empty opens, degrees above
the ambient dimension and the signed ambient point current remain covered.
The attained integral minimum of 4.2.18 and the characterisations of
4.1.28 are not assumed. No new source correction is claimed. See the
[item account](chapter4/4.1.md#item-4-1-24).

### 4.1.25 — Lipschitz images of summable currents

The 76 new theories passed ordinary registered compilation in
668.212s, complete recursive consumer kernel checking in
642.389s and all 131 new strict dependency queries in
420.289s. All 34,272 earlier assumption results are
preserved. The complete log has 34,403 entries and only the three
permitted boolp assumptions. An ordinary Rocq preflight confirms every new
public query name. See the [validation report](checkpoints/4.1.25-validation.json)
and [new-query log](checkpoints/4.1.25-assumptions.log).
The consumer root `Federer.CurrentLipschitzArea` reaches every new source.
No earlier mathematical proof source changed; no private proof object was
copied or adopted. The stages used the required switch, nice 10, umask
0002, group llm and group read/write under the automatic resource policy.

The release covers the assertions on p. 383: the Lebesgue action of the
Lipschitz image of a compactly supported summable current, the full-fibre
density with its existence for $\mathscr H^m$ almost all targets, its
measurability, summability and mass bound, the identity of the image
current with the Hausdorff density current, the associated approximate
tangent and the signed full-fibre formula. The first display is proved in
every degree. Simplicity of the density is asserted in positive degree;
the literal empty-product convention makes it fail in degree zero, as
an actual example on $\mathbf R^0$ proves. See the
[item account](chapter4/4.1.md#item-4-1-25).

### 4.1.26 — Degree of a Lipschitz map

The 34 new theories and the endpoint source passed ordinary registered
compilation in 414.937s, complete recursive consumer kernel checking in
1124.703s and all 66 new strict dependency queries in 1505.091s. All
34,403 earlier assumption results are preserved. The complete log has
34,469 entries and only the three permitted boolp assumptions. An
ordinary Rocq preflight confirms every new public query name. See the
[validation report](checkpoints/4.1.26-validation.json) and
[new-query log](checkpoints/4.1.26-assumptions.log). The consumer roots
`Federer.LipschitzDegree` and `FedererTests.LipschitzDegreeEndpointExamples`
reach every new source. A first audit attempt waited for memory admission
and was stopped before any query ran; it is retained and not promoted.
No earlier mathematical proof source changed; no private proof object was
copied or adopted. The stages used the required switch, nice 10, umask
0002, group llm and group read/write under the automatic resource policy.

The release covers the corollary on pp. 383–384: the signed degree of a
Lipschitzian map of $\mathbf R^m$ into itself on a bounded $\mathscr L^m$
measurable set, its almost-everywhere fibre formula, the identity
$f_\#(\mathbf E^m\mathbin{\llcorner}A)=\mathbf E^m\mathbin{\llcorner}(\operatorname{degree}f|A)$,
almost constancy on each component of $\mathbf R^m\sim f(\operatorname{Bdry}A)$,
and both consequences for connected $A$ and univalent $f|A$. No source
correction or new hypothesis is needed. See the
[item account](chapter4/4.1.md#item-4-1-26).

### 4.1.27 — The simplex as a cube image

The 42 new theories and the endpoint source passed ordinary registered
compilation in 395.632s, complete recursive consumer kernel checking in
672.674s and all 113 new strict dependency queries in 228.632s. All
34,469 earlier assumption results are preserved. The complete log has
34,582 entries and only the three permitted boolp assumptions. An
ordinary Rocq preflight confirms every new public query name. See the
[validation report](checkpoints/4.1.27-validation.json) and
[new-query log](checkpoints/4.1.27-assumptions.log). The consumer roots
`Federer.SimplexCubeCurrents` and `FedererTests.SimplexCubeEndpointExamples`
reach every new source. Two daytime build attempts were stopped before
completion and are retained and not promoted. No earlier mathematical
proof source changed; no private proof object was copied or adopted. At
the user's explicit one-off request, the stages used all available
processors and memory instead of the daytime limits, with the required
switch, nice 10, umask 0002, group llm and group read/write.

The release covers the remarks on p. 384: the prefix-product map $f$ of
the open unit cube $C$, the exact image $f(C)$ as the set of positive
barycentric combinations, univalence of $f|C$, the wedge formula for the
partial derivatives at every point of $\mathbf R^m$, the identity
$[u_0,\dots,u_m]=f_\#(\mathbf E^m\mathbin{\llcorner}C)$ and
$[u_0,\dots,u_m]=\mathscr H^m\wedge\eta$. The wedge formula uses the
published correction of p. 384, line 19. The literal univalence hypothesis
is qualified in the degenerate case $n+1<m$. See the
[item account](chapter4/4.1.md#item-4-1-27).

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

The [earlier documentation audit](checkpoints/documentation-audit.json)
records coverage, local source links, historical checkpoint labels and
error-list proof references as checked against the 3.3 release. Later item
reports record subsequent checks.

The [4.1.7 report](checkpoints/4.1.7-validation.json) includes the current
check of 123 Markdown files and 59,898 links, five rendered HTML
pages with mathematical notation, and the 135-entry error catalogue.
Three LaTeX passes produced stable references and no layout warnings.

The [checkpoint catalogue](checkpoints/README.md) lists the historical records.
The complete chronological build record remains in [verification.txt](verification.txt).
