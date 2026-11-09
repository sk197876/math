# Maintaining the documentation

[Documentation](toc.md) · [Item map](contents.md) · [Index](index.md) · [Symbols](symbols.md) · [Divergences](divergences.md) · [Bibliography](bibliography.md)

## Document structure

Start at [toc.md](toc.md). Keep one guide for each Federer section in
`chapter1/`, `chapter2/`, or `chapter3/`. Keep these paths stable: the maps,
source guide, and historical records link to them.

Each section guide has the following structure:

1. **Overview:** source editions, printed pages, coverage, and conventions.
2. **Contents:** links to its numbered items and supporting notes.
3. **Numbered items:** accounts in book order, with supporting parts grouped
   under their original item.
4. **Section notes**, when needed: shared interfaces, source conventions,
   coverage qualifications, and dated release notes.
5. **Navigation:** the documentation index and adjacent section guides.

Each item account states the formalised assertions, identifies their public
interfaces and declarations, explains proof adaptations, records hypotheses
and corrections, and links its validation evidence. Use a table when it
makes assertions and declarations easier to compare. Retain the mathematical
order when a proof needs a different exposition. Keep historical stages
labelled as such; a former partial stage does not override the final result.

The other guides have distinct roles:

| Guide | Contents and order |
| --- | --- |
| [contents.md](contents.md) | Generated item-to-file map, in book order |
| [index.md](index.md) | The printed index, followed by section supplements in book order |
| [symbols.md](symbols.md) | The printed notation lists, followed by section supplements in book order |
| [divergences.md](divergences.md) | Corrections, conventions, interpretations, and proof departures, by chapter and section |
| [bibliography.md](bibliography.md) | Stable citation keys; source entries in alphabetical order, followed by the writing guide |
| [references/README.md](references/README.md) | Editions, correction files, annotation history, and consulted passages by chapter |
| [validation.md](validation.md) | Dated release accounts and the scope of their checks |
| [checkpoints/README.md](checkpoints/README.md) | Catalogue of historical progress notes and validation reports |
| [rendering.md](rendering.md) | Commands for Markdown HTML and coqdoc |

Keep mathematical details in the section guides. The top-level
[README](../README.md) explains the project, sources, principles, coverage,
documentation, build environment, targets, and artifact storage.

## English and mathematical language

Follow [Strunk2011](bibliography.md#strunk2011), the text in the supplied
electronic edition. Give each paragraph one subject, put its main point
first, use concrete words and active verbs, and express parallel ideas in
parallel form. Omit needless words while retaining every mathematical
condition, source qualification, and limitation of the evidence.

Use the present tense for definitions, theorems, and current coverage. Use
the past tense for dated work and validation. Replace temporary phrases
such as “now includes” with a description of the result. Give the date
when a change of status matters. Keep verbatim quotations, mathematical
notation, declaration names, and precise source locators intact.

Use sentence case for headings and leave a blank line after each heading.
Use one title per page and consecutive heading levels. Keep table columns
consistent within each map, and keep table rows together without blank
lines. Escape literal vertical bars in table cells. Keep old heading
anchors when a heading moves or changes, so existing links still resolve.
The numbered items also have stable anchors such as `#item-3-4-6`.

Identify sources by citation keys in the [bibliography](bibliography.md),
with printed page and item locators. Keep local attachment paths out of
the documentation. The [source guide](references/README.md) distinguishes
Federer's corrections, project corrections, and supporting arguments.

## Updating the maps

After changing the formalisation, update the item in its section guide.
Record departures from Federer's text there and in
[divergences.md](divergences.md). Then run the following commands from the
repository root:

```sh
python3 tools/contents.py
python3 tools/linkify_docs.py
python3 tools/divergence_counts.py
```

The contents generator reads source annotations and numbered-item headings.
It lists up to six principal declarations per file, with theorems first.
It records historical source accounts without inventing proof files.
The linkify script links mentioned `.v` files and uniquely defined
declarations, and repairs declaration links whose line no longer contains
the declaration. Recompute divergence counts after changing the register.
Keep the Counts section last. Its generator rejects table rows placed
after the summary, so regeneration cannot silently discard them.

Update [index.md](index.md) and [symbols.md](symbols.md) when notions or
notations change. Check the source guide and error catalogue when a
correction changes. Review the top-level README and documentation index
for changes in coverage. The generators support this review; they do not
establish mathematical completeness.

## Checking the documentation

Python 3 and Pandoc are required. Run:

```sh
python3 docs/check_docs.py --report /tmp/federer-doc-links.json
python3 docs/check_docs.py --external --report /tmp/federer-doc-links-external.json
```

With no file arguments, the checker reads the top-level README and every
Markdown file under `docs/`, including historical notes. It checks local
file targets, Markdown headings, explicit HTML anchors, source-line ranges,
and code-formatted declaration labels against linked Rocq lines. It rejects duplicate
anchors. Use explicit file arguments for a focused check.

The second command also requests each distinct external HTTP URL. It
records redirects and reports HTTP errors and network failures separately
from broken local links. A failed request remains unresolved; a server
refusal does not establish that a bibliographical identifier is wrong.
External page fragments and the mathematical content of linked pages
require separate review.

After structural changes, render representative pages with the
[HTML converter](rendering.md#html-copies-of-markdown). Inspect tables,
mathematics, local navigation, and links between converted pages. Preserve
all assertions, hypotheses, source locators, declarations, qualifications,
and validation figures when reorganising existing text.

## Validation records and historical notes

Keep the results of actual builds and audits in
[verification.txt](verification.txt), [assumptions.log](assumptions.log),
and the corresponding [checkpoint records](checkpoints/README.md).
The [toolchain record](toolchain.txt) gives exact versions.

Historical records retain their dates, counts, worker limits, incidents,
and next-step instructions. Read those instructions as history, rather
than as the current work queue. Preserve the records when later work
supersedes them; link the later result from the current section guide.

At ordinary section releases, `tools/dependency_audit.py BASE` supports an
audit of changed dependencies. It does not replace a fresh full audit
when one is explicitly requested. The Chapter 2 full audit described in
the [verification guide](validation.md) is a completed historical release.

Documentation checks do not replace Rocq compilation, recursive kernel
checking, or assumptions audits after proof changes. A documentation-only
reorganisation does not provide new mathematical validation.
