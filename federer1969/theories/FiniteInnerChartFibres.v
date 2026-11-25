(** Federer (1969), 3.2.28, pp. 265–267:
    actual fibre sets and their Hausdorff masses are
    unchanged by orthonormal ambient coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerMetric
  FiniteInnerChartUP FiniteInnerChartCompact PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialMappingMultiplicity HausdorffMeasure HausdorffCountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_chart_fibre_set]: the actual
    fibres in the coarea and area applications of
    Federer 3.2.28, pp. 265–267. Only the
    original restricted function contributes, and both
    ambient charts satisfy actual inverse laws. *)
Lemma finite_inner_chart_fibre_set (R:realType) (V U:lmodType R)
    (B:V->V->R) (C:U->U->R) n k
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (a:Hom (R_n R k) U) (t:Hom U (R_n R k)) (S:set V) (F:V->U) y:
  is_finite_inner_chart B e p ->is_finite_inner_chart C a t ->
  partial_mapping_fibre (partial_function_source_restrict (p @` S)
    (partial_function_total (fun z=>t (F (e z))))) (t y)=p @` [set x|S x /\F x=y].
Proof.
move=>hChart hTarget; apply/seteqP; split=>z.
- move=>[[x hx <-] hF]; exists x; last reflexivity.
  split; first exact hx.
  change (t (F (e (p x)))=t y) in hF.
  rewrite (finite_inner_chart_right_inverse hChart) in hF.
  have h:=congr1 a hF.
  by rewrite !(finite_inner_chart_right_inverse hTarget) in h.
- move=>[x [hx hFx] <-]; split; first by exists x.
  change (t (F (e (p x)))=t y).
  by rewrite (finite_inner_chart_right_inverse hChart) hFx.
Qed.

(** Source for [finite_inner_chart_fibre_measure]: the
    actual fibre masses for Federer 3.2.28,
    pp. 265–267, preserved by 2.10.11,
    p. 176, in every natural Hausdorff degree. *)
Lemma finite_inner_chart_fibre_measure (R:realType) (V U:lmodType R)
    (B:V->V->R) (C:U->U->R) (hB:is_inner_product B) n k
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (a:Hom (R_n R k) U) (t:Hom U (R_n R k)) (S:set V) (F:V->U) y r:
  is_finite_inner_chart B e p ->is_finite_inner_chart C a t ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) r
    (partial_mapping_fibre (partial_function_source_restrict (p @` S)
      (partial_function_total (fun z=>t (F (e z))))) (t y))=
  @hausdorff_measure R (inner_metric_space hB) r [set x|S x /\F x=y].
Proof.
move=>hChart hTarget.
rewrite (@finite_inner_chart_fibre_set R V U B C n k e p a t S F y hChart hTarget).
exact:(@finite_inner_chart_inverse_hausdorff R V B hB n e p hChart r _).
Qed.

(** Source for [finite_inner_chart_fibre_multiplicity]:
    the exact fibre count in the square-map area
    calculation, Federer 3.2.28(4), p. 267.
    Counting agrees with H^0 by 2.10.2(2), p. 171. *)
Lemma finite_inner_chart_fibre_multiplicity (R:realType) (V U:lmodType R)
    (B:V->V->R) (C:U->U->R) (hB:is_inner_product B) n k
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (a:Hom (R_n R k) U) (t:Hom U (R_n R k)) (S:set V) (F:V->U) y:
  is_finite_inner_chart B e p ->is_finite_inner_chart C a t ->
  @partial_mapping_multiplicity R _ _ (partial_function_source_restrict (p @` S)
    (partial_function_total (fun z=>t (F (e z))))) (t y)=
  @CountingMeasure.counting_measure R V [set x|S x /\F x=y].
Proof.
move=>hChart hTarget.
have h:=@finite_inner_chart_fibre_measure R V U B C hB n k e p a t S F y 0 hChart hTarget.
rewrite !hausdorff_zero_counting_measure in h; exact h.
Qed.
