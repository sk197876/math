(** A local orthogonal axis for the projection comparison
    in Federer (1969), 3.2.45, pp. 279–280.
    Reuse the original sealed normal charts and
    normalization laws of 1.7.1–1.7.4, pp. 28–31. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerNormalization OrthogonalMaps EuclideanCoordinateSplit
  EuclideanNormalChartUP EuclideanNormalChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_vector_head_axis_exists]: supporting
    coordinate connection for the sharp projection comparison
    in Federer 3.2.45, pp. 279–280. Any
    original vector can be carried onto the scalar
    head axis by an actual orthogonal endomorphism.
    A nonzero vector uses the existing opaque
    normal chart of its normalized direction; zero
    uses the identity. The axis and map remain
    local existential data, with no chosen global operator. *)
Theorem euclidean_vector_head_axis_exists (R : realType) n (w : R_n R n.+1) :
  exists T : {linear R_n R n.+1 -> R_n R n.+1},
    is_orthogonal_map (@euclidean_inner_product R n.+1) (@euclidean_inner_product R n.+1) T /\
    @coordinate_tail R n (T w) = 0.
Proof.
case: (eqVneq w 0)=> [hZero|hNonzero].
- exists (linear_id (R_n R n.+1)); split; first exact: orthogonal_identity.
  rewrite hZero linear0; apply/ffunP=> i.
  by rewrite /coordinate_tail !ffunE.
- pose hB := @euclidean_inner_productP R n.+1.
  pose u := inner_normalize hB w.
  have hU : euclidean_inner_product u u= 1 := inner_normalize_square hB hNonzero.
  pose D := euclidean_normal_chart ord0 hU.
  have hD := euclidean_normal_chart_specification ord0 hU.
  pose T := normal_chart_backward_map D.
  have hT : is_orthogonal_map (@euclidean_inner_product R n.+1)
      (@euclidean_inner_product R n.+1) T.
    exact: orthogonal_inverse (normal_chart_orthogonal_law hD) (normal_chart_backward_inverse_law hD).
  exists T; split=> //.
  have hAxis : T u = @coordinate_basis R n.+1 ord0.
    by rewrite /T -(normal_chart_axis_law hD) (normal_chart_forward_inverse_law hD).
  have hW : T w = (inner_norm hB w)*:(@coordinate_basis R n.+1 ord0).
    have h := congr1 T (inner_normalizeK hB hNonzero).
    rewrite linearZ hAxis in h; exact (esym h).
  rewrite hW; apply/ffunP=> i.
  by rewrite /coordinate_tail /coordinate_basis !ffunE lift_eqF scaler0.
Qed.
