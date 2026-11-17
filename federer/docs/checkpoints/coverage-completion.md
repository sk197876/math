# Coverage completion

## Scope

The proof and coverage supplements complete the gaps identified after
the Chapter 3 release, in Federer's stated generality. Explicit omissions are: 1.1.3, the excluded examples of 2.8.8–9, the deferred
material of 2.10.46, Kneser’s second paragraph of 3.2.40, and the Ward
construction cited in 2.10.27. Historical questions and commentary do not
become theorem obligations.

The baseline full-project validation is recorded in
[the full-project report](chapter3-full-validation.json).
No new proof is certified by that earlier validation.

## Method

The proof review uses Federer's actual passage, preceding pages, earlier enumerated
conclusions and earlier subsection items. It identifies intended
dependencies and reuses existing formal statements after checking their
hypotheses, scalar fields, conventions, endpoints and opaque interfaces.
Only missing connections or extensions require new proofs. Checked
counterexamples to false printed assertions remain part of the account.

## Completion queue

| Item | Assertion | Status |
| --- | --- | --- |
| 1.4.4 | General corrected coefficient noninjectivity | Complete; [supplement validation](1.4.4-supplement-validation.json) passed |
| 1.4.5 | Sharp exceptional-case classification for the ordinary tensor product | Complete; [supplement validation](1.4.5-supplement-validation.json) passed |
| 2.10.11 | Real-dimensional Hausdorff bound and spherical variant | Complete with a proved correction of the false spherical parenthesis; [supplement validation](2.10.11-supplement-validation.json) passed |
| 2.10.17(3) | Original partial-quotient assertion | Complete; [supplement validation](2.10.17-supplement-validation.json) passed |
| 2.10.19 | Five real-dimensional density estimates | Complete; [supplement validation](2.10.19-supplement-validation.json) passed |
| 2.10.24 | Real-dimensional Hausdorff and spherical applications | Complete; [supplement validation](2.10.24-supplement-validation.json) passed |
| 2.10.25 | Real-dimensional fibre bound | Complete; [supplement validation](2.10.25-supplement-validation.json) passed |
| 2.10.26 | Real-dimensional fibre measurability | Complete; [supplement validation](2.10.26-supplement-validation.json) passed |
| 2.10.27 | Real-dimensional section/product inequalities and cited nonreplacement assertion | All three original real-degree inequalities registered and validated; [spherical supplement](2.10.27-supplement-validation.json). The user intentionally omitted the cited Ward construction |
| 2.10.28 | Standard Hausdorff identification of the power-gauge application | Complete; [supplement validation](2.10.28-supplement-validation.json) passed |
| 2.10.29 | Actual Gamma-normalized Hausdorff conclusions | Complete; [supplement validation](2.10.29-supplement-validation.json) passed |
| 2.10.42 | Real-dimensional spherical/Hausdorff comparison | Complete; [supplement validation](2.10.42-supplement-validation.json) passed |
| 2.10.45 | Real-dimensional Euclidean-factor product theorem | Complete; [supplement validation](2.10.45-supplement-validation.json) passed |
| 3.2.45 | Full mixed-volume comparisons, exponent continuity and Gillespie products | Complete original continuity, sharp comparisons, full bounded-convex ordinary section integral, all-set Gillespie section upper integral and measurable-first-factor product equality; [section/product validation](3.2.45-sections-supplement-validation.json). The false printed quantitative estimate retains its proved correction |
| 2.10.6 | Assemble the nonexcluded comparison assertions using the completed dependencies | Complete original diagram, coefficient bounds, bounded and unbounded ratios, original examples and ambient/rectifiable agreements; [supplement validation](2.10.6-supplement-validation.json) passed |
| 3.4.8(5), proof | Stronger sigma-compactness assertion for the original reduction sets | Original real assertion complete for arbitrary proper ideals; [supplement validation](3.4.8-auxiliary-supplement-validation.json) passed |


## Ward citation: intentional omission

All nonomitted entries in the table passed their recorded registered checks.
The Ward construction cited in 2.10.27 is intentionally omitted at the
user's request. Federer supplies no construction there: on printed p. 190,
he cites [Ward1964](../bibliography.md#ward1964) for the failure of replacing
both spherical measures by Hausdorff measures. All three original
inequalities are proved. The explicit Cantor products in 2.10.29,
pp. 193–195, are also proved.

The [omission account](2.10.27-ward-omission.md) states the proof limit.
Unfinished drafts are outside the registered library and this snapshot.
