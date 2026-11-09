# Verification and release records

[Documentation](toc.md) · [Item map](contents.md) · [Index](index.md) · [Symbols](symbols.md) · [Divergences](divergences.md) · [Bibliography](bibliography.md)

## How to read the records

Compilation, recursive kernel checking, and assumptions audits establish
the recorded statements under their recorded hypotheses. Coverage and
source qualifications remain part of each [section account](toc.md).
A historical validation does not validate later changes or private drafts.

The accounts below retain the release descriptions previously spread
through the project README and documentation index. They describe this
checkout through the 6 November 2026 release of 3.4.6. Later completion
claims require their own registered sources and validation records.

## Coverage and verification recorded in the project README

Chapter 1 covers §§1.2–1.10 with the qualifications in the section accounts;
§1.1.1, §1.1.2 and §1.1.4 are complete; §1.1.3 is intentionally left aside. Chapter 2
reaches the requested last proof, **2.10.48**. Sections 2.1–2.7 and 2.9
are covered as documented. §§2.8.8–2.8.9 are complete within the requested scope: subsidiary assertions
and strict-convexity uniqueness are included, and book examples are excluded.
Item 2.10.2 is complete, including actual Gamma normalization in every
nonnegative real degree and the printed circle cutoff counterexample.
Remaining qualifications include 2.10.6 and the listed variants of later items. **2.10.46 remains partial and
deferred at the user's request.** Item 2.10.49 is a historical remark
requiring no formalisation. Chapter 2 is therefore not claimed to contain
a proof of every printed mathematical assertion.

The final compact-subset and Suslin inner-approximation results cover the
exact natural-degree Hausdorff normalisation and arbitrary nonnegative
real power gauges with explicit positive coefficients. Detailed statements,
coverage limits and proof accounts belong in the
[section documentation](toc.md).

The **27 October 2026 release passed** the complete Chapter 2 rebuild,
full recursive kernel check and fresh audit of all 15,349 assumption queries.
The rebuild reused compatible unchanged Chapter 1 artifacts from Claude.

The [scheduled full-project validation](checkpoints/2026-10-28-full-validation.json)
completed on **29 October 2026**. It passed a fresh clean rebuild of the
whole registered project, recursive kernel checking and all 15,729
assumptions queries, without warnings or changed assumption sets. Its
snapshot included the partial 3.1.4 checkpoint; later proofs receive
separate focused checks.

The [latest clean full-project validation](checkpoints/2026-11-02-full-validation.json)
finished on **3 November 2026**: all 7,660 registered modules and 20,465
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
assumptions audit. [Subsection 3.2](chapter3/3.2.md) is in progress: items
3.2.1–3.2.39 are complete and validated, with explicit source qualifications and
corrections in the section account. The first paragraph of 3.2.40 passed the full
validation completed on 3 November 2026; only its Kneser example remains deferred. Items
3.2.41–44 and 3.2.46–48 are complete and validated. Item 3.2.45 is partial outside the
current request. [Subsection 3.3](chapter3/3.3.md) is complete with the documented
source corrections and qualifications: mathematical items 3.3.1–3.3.10 and 3.3.12–3.3.21
are validated, and historical items 3.3.11 and 3.3.22 have source accounts. [Subsection 3.4](chapter3/3.4.md) is in progress: 3.4.1–3.4.6 are validated, including critical values, sharpness, analytic germs, conditional local algebra and Weierstrass division and preparation.
The algebra theorems in finite dimension and analytic stratification remain. See the [3.4.6 validation record](checkpoints/3.4.6-validation.json).
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

The 27 October 2026 release passed the Chapter 2 rebuild, full recursive
kernel check and fresh 15,349-query assumptions audit. Unchanged Chapter 1
artifacts were reused after fingerprint checks. See the
[verification record](verification.txt) and
[machine-readable release report](checkpoints/chapter2-release-validation.json).

The [clean full-project validation](checkpoints/2026-11-02-full-validation.json)
finished on 3 November 2026 with all 7,660 registered modules and 20,465
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
maps](chapter3/3.2.md) is in progress; items 3.2.1–3.2.39 are complete and validated,
with explicit source qualifications and corrections in the section account. The first
paragraph of 3.2.40 passed the full validation completed on 3 November 2026; only its
Kneser example remains deferred. Items 3.2.41–44 and 3.2.46–48 are complete and
validated. Item 3.2.45 is partial outside the current request. [Subsection
3.3](chapter3/3.3.md) is complete with the documented source corrections and
qualifications: mathematical items 3.3.1–3.3.10 and 3.3.12–3.3.21 are validated, and
historical items 3.3.11 and 3.3.22 have source accounts. [Subsection 3.4](chapter3/3.4.md) is in progress: 3.4.1–3.4.6 are validated, including critical values, sharpness, analytic germs, conditional local algebra and Weierstrass division and preparation.
The algebra theorems in finite dimension and analytic stratification remain. See the [3.4.6 validation record](checkpoints/3.4.6-validation.json).
Chapter 3 is exposed through [`Rectifiability.v`](../theories/Rectifiability.v) and tested in
[`DifferentialExamples.v`](../tests/DifferentialExamples.v) and [`InverseFunctionExamples.v`](../tests/InverseFunctionExamples.v).

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

## Individual release records

The [full-project validation](checkpoints/2026-11-02-full-validation.json) completed on 3 November 2026: all 7,660 registered modules rebuilt cleanly, complete recursive kernel checking and all 20,465 fresh assumption queries passed without warnings; all 20,393 earlier assumption sets were preserved. This does not extend coverage to unregistered drafts.

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

The [9 November reorganisation record](checkpoints/2026-11-09-documentation-reorganisation.json)
records preservation checks, link checks, HTML rendering, and the revision
of the error catalogue. This documentation work changes no proof source
and provides no new mathematical validation.

The [5 November documentation audit](checkpoints/2026-11-05-documentation-audit.json)
checks current coverage, local source links, historical checkpoint labels and
the error-list proof references against the validated formalisation.

The [checkpoint catalogue](checkpoints/README.md) lists the dated records.
The complete chronological build record remains in [verification.txt](verification.txt).
