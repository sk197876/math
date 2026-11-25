(** Public orthogonal normal charts supporting Federer (1969), 2.10.30, p.
    195. Downstream proofs use only the opaque chart's inverse,
    orthogonality and prescribed-axis laws. Source context:
    EuclideanNormalChartUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  OrthogonalMaps EuclideanNormalChartUP EuclideanNormalChartSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_normal_chart]: supporting
    abstract coordinate chart for the general normal
    direction of 2.10.30, p. 195. *)
Definition euclidean_normal_chart (R : realType) n (j : 'I_n) (u : R_n R n)
  (hu : euclidean_inner_product u u= 1) := @EuclideanNormalChart.value R n j u hu.
Arguments euclidean_normal_chart {R n} j {u} hu.

(** Source for [euclidean_normal_chart_specification]: supporting
    orthogonal chart laws for 2.10.30, p. 195. *)
Lemma euclidean_normal_chart_specification (R : realType) n (j : 'I_n) (u : R_n R n)
  (hu : euclidean_inner_product u u= 1) :
  @is_euclidean_normal_chart R n j u (euclidean_normal_chart j hu).
Proof. exact: EuclideanNormalChart.laws. Qed.
Arguments euclidean_normal_chart_specification {R n} j {u} hu.

(** Source for [euclidean_normal_chart_forward]: supporting
    orthogonal coordinate-to-normal map for 2.10.30,
    p. 195. *)
Definition euclidean_normal_chart_forward (R : realType) n (j : 'I_n) (u : R_n R n)
  (hu : euclidean_inner_product u u= 1) := normal_chart_forward_map (euclidean_normal_chart j hu).
Arguments euclidean_normal_chart_forward {R n} j {u} hu.

(** Source for [euclidean_normal_chart_backward]: supporting
    inverse normal-coordinate map for 2.10.30, p. 195. *)
Definition euclidean_normal_chart_backward (R : realType) n (j : 'I_n) (u : R_n R n)
  (hu : euclidean_inner_product u u= 1) := normal_chart_backward_map (euclidean_normal_chart j hu).
Arguments euclidean_normal_chart_backward {R n} j {u} hu.

(** Source for [euclidean_normal_chart_forwardK]: supporting
    first inverse-coordinate law for 2.10.30, p. 195. *)
Lemma euclidean_normal_chart_forwardK (R : realType) n (j : 'I_n) (u : R_n R n)
  (hu : euclidean_inner_product u u= 1) :
  cancel (euclidean_normal_chart_forward j hu) (euclidean_normal_chart_backward j hu).
Proof. exact: normal_chart_forward_inverse_law (euclidean_normal_chart_specification j hu). Qed.

(** Source for [euclidean_normal_chart_backwardK]: supporting
    reverse inverse-coordinate law for 2.10.30, p. 195. *)
Lemma euclidean_normal_chart_backwardK (R : realType) n (j : 'I_n) (u : R_n R n)
  (hu : euclidean_inner_product u u= 1) :
  cancel (euclidean_normal_chart_backward j hu) (euclidean_normal_chart_forward j hu).
Proof. exact: normal_chart_backward_inverse_law (euclidean_normal_chart_specification j hu). Qed.

(** Source for [euclidean_normal_chart_orthogonal]: supporting
    orthogonality of the normal chart for 2.10.30,
    p. 195. Volume preservation is derived from
    this law, rather than included in the specification. *)
Lemma euclidean_normal_chart_orthogonal (R : realType) n (j : 'I_n) (u : R_n R n)
  (hu : euclidean_inner_product u u= 1) :
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n)
    (euclidean_normal_chart_forward j hu).
Proof. exact: normal_chart_orthogonal_law (euclidean_normal_chart_specification j hu). Qed.

(** Source for [euclidean_normal_chart_axis]: supporting prescribed normal
    direction in 2.10.30, p. 195 *)
Lemma euclidean_normal_chart_axis (R : realType) n (j : 'I_n) (u : R_n R n)
  (hu : euclidean_inner_product u u= 1) :
  euclidean_normal_chart_forward j hu (@coordinate_basis R n j)=u.
Proof. exact: normal_chart_axis_law (euclidean_normal_chart_specification j hu). Qed.
