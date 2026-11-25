(** Opaque orthogonal-chart witness supporting Federer (1969), 2.10.30, p.
    195. Expose only the specified inverse, orthogonality and axis laws.
    Source context: EuclideanNormalChartUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  EuclideanNormalChartUP EuclideanNormalChartConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type EUCLIDEAN_NORMAL_CHART.
(** Source for [value]: supporting orthogonal normal
    chart for 2.10.30, p. 195, specified
    independently of its existence witness. *)
Parameter value : forall (R : realType) n (j : 'I_n) (u : R_n R n),
  euclidean_inner_product u u= 1 -> euclidean_normal_chart_data R n.
(** Source for [laws]: supporting normal-chart laws
    used for arbitrary directions in 2.10.30, p. 195. *)
Parameter laws : forall (R : realType) n (j : 'I_n) (u : R_n R n)
  (hu : euclidean_inner_product u u= 1),
  @is_euclidean_normal_chart R n j u (@value R n j u hu).
End EUCLIDEAN_NORMAL_CHART.
Module EuclideanNormalChart : EUCLIDEAN_NORMAL_CHART.
(** Source for [value]: proved chart existence
    witness for 2.10.30, p. 195, hidden
    by opaque module ascription. *)
Definition value (R : realType) n (j : 'I_n) (u : R_n R n)
  (hu : euclidean_inner_product u u= 1) :=
  projT1 (cid (@euclidean_normal_chart_exists R n j u hu)).
(** Source for [laws]: proved abstract normal-chart
    laws supporting 2.10.30, p. 195. *)
Lemma laws (R : realType) n (j : 'I_n) (u : R_n R n)
  (hu : euclidean_inner_product u u= 1) :
  @is_euclidean_normal_chart R n j u (@value R n j u hu).
Proof. exact: (projT2 (cid (@euclidean_normal_chart_exists R n j u hu))). Qed.
End EuclideanNormalChart.
