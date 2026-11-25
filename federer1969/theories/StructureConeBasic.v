(** Consequences of the exact cone definition in Federer (1969),
    3.3.1, p. 287. Use only the public cone and distance laws;
    the vertex is excluded and every radius, including infinity,
    keeps the printed strict upper bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations GrassmannSubspaces
  EuclideanInnerProduct InnerMetric InnerNorm MetricSetDistanceUP
  MetricSetDistanceSealed MetricSetDistanceBasic StructureConeUP StructureCone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_plane_nonempty]: the vector plane V
    in the definition of Federer 3.3.1, p. 287, contains zero.
    This supplies the nonempty-set premise of the existing real
    distance interface, including zero-dimensional planes. *)
Lemma structure_plane_nonempty (R:realType) n k (V:G (R_n R n) k):
  ([set x:inner_metric_space (@euclidean_inner_productP R n)|grassmann_val V x] !=set0).
Proof. exists 0; exact:subspace_zero. Qed.

(** Source for [structure_cone_norm_bound]: the strict norm-radius
    inequality in the first display of Federer 3.3.1, p. 287.
    This supporting consequence includes an infinite radius. *)
Lemma structure_cone_norm_bound (R:realType) n k (V:G (R_n R n) k)
    (a x:inner_metric_space (@euclidean_inner_productP R n)) (r: \bar R) (s:R):
  structure_cone V a r s x ->
  ((inner_norm (@euclidean_inner_productP R n) (x-a))%:E<r)%E.
Proof.
move=>hx.
have hd:=@MetricSetDistance.laws R (inner_metric_space (@euclidean_inner_productP R n))
  [set y:inner_metric_space (@euclidean_inner_productP R n)|grassmann_val V y]
  (structure_plane_nonempty V).
have h:=((@structure_cone_specification R n k V a r s) _ hd x).1 hx.
exact:h.2.
Qed.

(** Source for [structure_cone_vertex_excluded]: strictness of the
    first inequality in Federer 3.3.1, p. 287, excludes a itself.
    It is not necessary to add a noncentral-point premise. *)
Lemma structure_cone_vertex_excluded (R:realType) n k (V:G (R_n R n) k)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (r: \bar R) (s:R):
  ~structure_cone V a r s a.
Proof.
move=>ha.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose A:set E:=[set y|grassmann_val V y].
have hA:A!=set0:=structure_plane_nonempty V.
pose d:=@MetricSetDistance.value R E A hA.
have hd:=@MetricSetDistance.laws R E A hA.
have h0:d 0=0.
  apply:(metric_set_distance_member hd); exact:subspace_zero.
have [hBad _]:=((@structure_cone_specification R n k V a r s) d hd a).1 ha.
by rewrite subrr h0 inner_norm0 mulr0 ltxx in hBad.
Qed.

(** Source for [structure_cone_radius_mono]: monotonicity in
    the radius in the definition of Federer 3.3.1, p. 287.
    All inequalities remain strict at the original source point. *)
Lemma structure_cone_radius_mono (R:realType) n k (V:G (R_n R n) k)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (r t: \bar R) (s:R):
  (r<=t)%E ->structure_cone V a r s `<=` structure_cone V a t s.
Proof.
move=>hrt x hx.
have hd:=@MetricSetDistance.laws R (inner_metric_space (@euclidean_inner_productP R n))
  [set y:inner_metric_space (@euclidean_inner_productP R n)|grassmann_val V y]
  (structure_plane_nonempty V).
have [hAngle hRadius]:=((@structure_cone_specification R n k V a r s) _ hd x).1 hx.
apply/((@structure_cone_specification R n k V a t s) _ hd x); split=>//.
exact:lt_le_trans hRadius hrt.
Qed.
