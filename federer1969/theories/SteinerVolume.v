(** Federer (1969), 2.10.30, p. 195: compact S and its Steiner
    symmetrisation have equal Euclidean volume. Follow the printed Fubini
    argument: normal scalar sections have equal lengths, and orthogonal
    product coordinates preserve Lebesgue measure. Compactness of T has
    already been proved from the section laws. Here the book's compact-set
    hypothesis is retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanNormalChartUP EuclideanNormalChart EuclideanNormalBlockCoordinates EuclideanNormalBlockMeasure
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes LebesgueScalarMeasure
  CenteredSectionUP SteinerSymmetrisationUP SteinerCompact TopologicalBorel
  MeasureUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_normal_chart_preserves_volume]: supporting
    volume equality in any orthogonal normal chart
    for 2.10.30, p. 195. The proof uses
    only the chart and symmetrisation specifications. *)
Theorem steiner_normal_chart_preserves_volume (R : realType) n
    (u : inner_metric_space (@euclidean_inner_productP R (n+1)))
    (S T : set (inner_metric_space (@euclidean_inner_productP R (n+1))))
    (D : euclidean_normal_chart_data R (n+1)) :
  @is_euclidean_normal_chart R (n+1) (rshift n (ord0 : 'I_1)) u D ->
  is_steiner_symmetrisation (@euclidean_inner_productP R (n+1)) u S T ->
  compact S -> euclidean_lebesgue_measure (n+1) S=euclidean_lebesgue_measure (n+1) T.
Proof.
move=> hD hT hS.
have hTc := steiner_preserves_compactness hT hS.
have hSm : measure_measurable (@euclidean_lebesgue_measure R (n+1)) S.
  apply: euclidean_borel_measurable; apply: closed_borel_set.
  exact: compact_closed (@metric_hausdorff R (inner_metric_space (@euclidean_inner_productP R (n+1)))) hS.
have hTm : measure_measurable (@euclidean_lebesgue_measure R (n+1)) T.
  apply: euclidean_borel_measurable; apply: closed_borel_set.
  exact: compact_closed (@metric_hausdorff R (inner_metric_space (@euclidean_inner_productP R (n+1)))) hTc.
have hiS := @euclidean_normal_section_integral R n u D hD S hSm.
have hiT := @euclidean_normal_section_integral R n u D hD T hTm.
have he : (fun p=>lebesgue_scalar_measure
    (normal_scalar_section u S (@euclidean_normal_block_join R n D (p,0))))=
    (fun p=>lebesgue_scalar_measure
    (normal_scalar_section u T (@euclidean_normal_block_join R n D (p,0)))).
  apply: funext=> p.
  exact (esym (centered_section_length_law (steiner_normal_sections_law hT
    (@euclidean_normal_block_base R n D u hD p)))).
rewrite -he in hiT; exact (measure_integral_unique hiS hiT).
Qed.

(** Source for [steiner_preserves_euclidean_volume]: direct
    equality L^n(S)=L^n(T) for compact S
    in 2.10.30, p. 195, for every ambient
    dimension. The zero-dimensional unit-normal case
    is impossible rather than assigned a fictitious
    hyperplane or line direction. *)
Theorem steiner_preserves_euclidean_volume (R : realType) n :
  forall (u : inner_metric_space (@euclidean_inner_productP R n))
    (S T : set (inner_metric_space (@euclidean_inner_productP R n))),
  is_steiner_symmetrisation (@euclidean_inner_productP R n) u S T ->
  compact S -> euclidean_lebesgue_measure n S=euclidean_lebesgue_measure n T.
Proof.
case: n=> [|n].
- move=> u S T hT hS.
  have hu := steiner_unit_normal_law hT.
  rewrite /euclidean_inner_product big_ord0 in hu.
  have hh : (0 : R)!=1 by rewrite eq_sym oner_eq0.
  by move/eqP: hu; rewrite (negbTE hh).
- rewrite -(addn1 n)=> u S T hT hS.
  have hu := steiner_unit_normal_law hT.
  pose j := rshift n (ord0 : 'I_1).
  pose D := euclidean_normal_chart j hu.
  exact (@steiner_normal_chart_preserves_volume R n u S T D
    (euclidean_normal_chart_specification j hu) hT hS).
Qed.
