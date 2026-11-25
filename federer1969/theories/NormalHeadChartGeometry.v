(** Federer (1969), 2.10.36, printed p. 198: choose coordinates whose first
    axis is the given chord direction. Derive their scalar coordinate,
    hyperplane foot and normal line identities from the existing abstract
    orthogonal-chart laws. No chart implementation is inspected. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerProductUP InnerMetric
  CoordinateProjection OrthonormalFamilies UnitNormalGeometry EuclideanCoordinateSplit EuclideanCoordinateTopology EuclideanNormalChartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_head_inclusion_axis]: supporting
    scalar-axis identity for the chosen
    projection in 2.10.36, p. 198.
    This is a consequence of the
    public coordinate-inclusion formula. *)
Lemma coordinate_head_inclusion_axis (R : realType) (n : nat) (t : R) :
  @coordinate_head_inclusion R n t=t*:(@coordinate_basis R n.+1 ord0).
Proof.
apply/ffunP=> i; rewrite /coordinate_head_inclusion /coordinate_basis !ffunE.
case: (i==ord0); last by rewrite scaler0.
change (t=t*1); by rewrite mulr1.
Qed.

(** Source for [coordinate_tail_continuous]: supporting
    continuity of the perpendicular coordinate projection
    used in 2.10.36, p. 198.
    Each coordinate is an existing continuous Euclidean
    coordinate functional; the empty target is included. *)
Lemma coordinate_tail_continuous (R : realType) (n : nat) :
  continuous (@coordinate_tail R n :
    inner_metric_space (@euclidean_inner_productP R n.+1) ->
    inner_metric_space (@euclidean_inner_productP R n)).
Proof.
apply: euclidean_map_continuous=> i.
have he : (fun x : inner_metric_space (@euclidean_inner_productP R n.+1) =>
    coordinate_tail x i)=(fun x => x (lift ord0 i)).
  by apply: funext=> x; rewrite /coordinate_tail ffunE.
rewrite he; exact: euclidean_coordinate_continuous.
Qed.

Section HeadChart.
Variable R : realType.
Variable n : nat.
Variable u : inner_metric_space (@euclidean_inner_productP R n.+1).
Variable D : euclidean_normal_chart_data R n.+1.
Hypothesis hD : @is_euclidean_normal_chart R n.+1 ord0 u D.
Local Notation f := (normal_chart_forward_map D).
Local Notation g := (normal_chart_backward_map D).
Local Notation hB := (@euclidean_inner_productP R n.+1).

(** Source for [normal_chart_head_coordinate]: supporting
    scalar coordinate along the chord normal
    used in 2.10.36, p. 198.
    It follows from the prescribed axis,
    inverse and orthogonality laws alone. *)
Lemma normal_chart_head_coordinate (x : inner_metric_space hB) :
  inner_coordinate hB u x=coordinate_head (g x).
Proof.
rewrite inner_coordinateE /coordinate_head.
have hh := normal_chart_orthogonal_law hD (@coordinate_basis R n.+1 ord0) (g x).
rewrite (normal_chart_axis_law hD) (normal_chart_backward_inverse_law hD) in hh.
rewrite (inner_symmetric hB x u) hh (inner_symmetric hB) euclidean_inner_basis; reflexivity.
Qed.

(** Source for [normal_chart_head_foot]: supporting
    zero normal coordinate of the projected
    point in 2.10.36, p. 198.
    The remaining coordinates are exactly the
    tail of the backward chart. *)
Lemma normal_chart_head_foot (x : inner_metric_space hB) :
  g (normal_foot hB u x)=euclidean_join (coordinate_tail (g x),0).
Proof.
have hgu : g u=@coordinate_basis R n.+1 ord0.
  by rewrite -(normal_chart_axis_law hD) (normal_chart_forward_inverse_law hD).
rewrite /normal_foot linearB linearZ hgu normal_chart_head_coordinate.
rewrite /euclidean_join /= linear0 addr0 -coordinate_head_inclusion_axis.
have hh := coordinate_decomposition (g x).
by rewrite -{1}hh addrAC subrr add0r.
Qed.

(** Source for [normal_chart_head_line]: supporting
    normal-line formula for the centred
    chord in 2.10.36, p. 198.
    This is derived for any specified
    chart with the first prescribed axis. *)
Lemma normal_chart_head_line (x : inner_metric_space (@euclidean_inner_productP R n)) (t : R) :
  f (euclidean_join (x,t))=f (euclidean_join (x,0))+t*:u.
Proof.
rewrite /euclidean_join /= linear0 addr0 linearD coordinate_head_inclusion_axis linearZ
  (normal_chart_axis_law hD); reflexivity.
Qed.
End HeadChart.
