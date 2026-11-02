(** Federer (1969), 2.9.16, p. 161: the counterexample using all closed
    balls containing the base point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring num_normedtype.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates CoordinateProjection
  EuclideanInnerProduct InnerProductUP InnerProductLaws Bilinear InnerNorm InnerMetric
  EuclideanCoordinateMetric EuclideanCoordinateTopology MetricClosedBalls TopologicalBorel
  MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic MeasureFiniteClosure LebesgueScalarMeasure EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.


Section Lines.
Variable R : realType.
Variable n : nat.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Variable i : 'I_n.
Variable v : E.
Local Notation f := (euclidean_coordinate_line i v).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation eps := (@coordinate_basis R n).

(** Source for [euclidean_affine_coordinate_line]: the straight
    line Y in Federer 2.9.16, p. 161, chosen in a
    coordinate direction in Euclidean space. Its translate and
    dimension are arbitrary; a second coordinate is required only
    for the tangent-ball and ambient-nullity conclusions. *)
Definition euclidean_affine_coordinate_line : set E := f @` setT.

(** Source for [euclidean_affine_coordinate_line_coordinates]:
    supporting coordinate description of Y in Federer 2.9.16,
    p. 161. Exactly the coordinates other than i are fixed;
    this description also covers the one-dimensional ambient space. *)
Lemma euclidean_affine_coordinate_line_coordinates (x : E) :
  euclidean_affine_coordinate_line x <-> forall j, j != i -> x j=v j.
Proof.
split.
- move=> [t _ <-] j hji.
  rewrite /euclidean_coordinate_line /coordinate_basis !ffunE (negbTE hji).
  change (v j+t*0=v j).
  by rewrite mulr0 addr0.
- move=> hx; exists (x i-v i)%R=> //; apply/ffunP=> j.
  rewrite /euclidean_coordinate_line /coordinate_basis !ffunE.
  change (v j+(x i-v i)*(if j==i then 1 else 0)=x j).
  case: (eqVneq j i)=> [->|hji]; first by rewrite mulr1 addrC subrK.
  by rewrite mulr0 addr0 hx.
Qed.

(** Source for [euclidean_affine_coordinate_line_closed]:
    supporting closedness of the straight line Y in Federer
    2.9.16, p. 161; the line is an intersection
    of closed coordinate level sets. This is topology background,
    not a new numbered assertion in the book. *)
Lemma euclidean_affine_coordinate_line_closed : closed euclidean_affine_coordinate_line.
Proof.
have he : euclidean_affine_coordinate_line =
    \bigcap_(j in [set j : 'I_n | j != i]) [set x : E | x j=v j].
  apply/seteqP; split=> x.
  - move=> /euclidean_affine_coordinate_line_coordinates hx j hj; exact: hx.
  - move=> hx; apply/euclidean_affine_coordinate_line_coordinates=> j hj; exact: hx j hj.
rewrite he; apply: closed_bigI=> j _.
apply: (@preimage_closed E R^o (fun x => x j) [set v j]); last exact: closed_eq.
by move=> x _; exact: euclidean_coordinate_continuous.
Qed.

(** Source for [euclidean_affine_coordinate_line_borel]:
    supporting Borelness of the line Y in Federer 2.9.16,
    p. 161, used to restrict Hausdorff length while preserving
    Borel regularity. *)
Lemma euclidean_affine_coordinate_line_borel : borel_set euclidean_affine_coordinate_line.
Proof. exact: closed_borel_set euclidean_affine_coordinate_line_closed. Qed.

(** Source for [euclidean_affine_coordinate_line_null]: direct
    ambient-nullity assertion L^n(Y)=0 in Federer 2.9.16,
    p. 161, for the chosen Euclidean coordinate line in
    every dimension with a second coordinate. A containing
    coordinate hyperplane has zero product measure by 2.6.5. *)
Lemma euclidean_affine_coordinate_line_null (j : 'I_n) : j != i ->
  euclidean_lebesgue_measure n euclidean_affine_coordinate_line=0%E.
Proof.
move=> hji; pose A k := if k==j then [set v j] else @setT R.
have hA k : measure_measurable (@lebesgue_scalar_measure R) (A k).
  rewrite /A; case: (k==j); last exact: measure_measurable_whole (lebesgue_scalar_is_measure R).
  exact (@measure_null_measurable R R (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) [set v j] (lebesgue_scalar_singleton (v j))).
have [_ hv] := @euclidean_coordinate_box_measure R n A hA.
have hz : euclidean_lebesgue_measure n (euclidean_coordinate_box A)=0%E.
  by rewrite hv (bigD1 j) //= /A eqxx lebesgue_scalar_singleton mul0e.
apply: (@measure_null_subset R E _ (euclidean_lebesgue_is_measure R n) _ _ _ hz).
move=> x /euclidean_affine_coordinate_line_coordinates hx k; rewrite /A.
case: (eqVneq k j)=> [->|hkj] //; exact: hx j hji.
Qed.

(** Source for [euclidean_coordinate_tangent_ball]: supporting tangent-ball
    construction in Federer 2.9.16, p. 161 Here the intersection with Y is
    exactly one point, for every positive radius and distinct coordinate
    directions i,j. *)
Lemma euclidean_coordinate_tangent_ball (j : 'I_n) (s r : R) :
  j != i -> (0<r)%R ->
  let a : E := f s+r*:(@coordinate_basis R n j) in
  metric_closed_ball a r (f s) /\
  euclidean_affine_coordinate_line `&` metric_closed_ball a r = [set f s].
Proof.
move=> hji hr a.
have hij : i != j by rewrite eq_sym.
have heii : B (eps i) (eps i) = 1.
  by rewrite euclidean_inner_basis /coordinate_basis ffunE eqxx.
have hejj : B (eps j) (eps j) = 1.
  by rewrite euclidean_inner_basis /coordinate_basis ffunE eqxx.
have heij : B (eps i) (eps j)=0.
  by rewrite euclidean_inner_basis /coordinate_basis ffunE (negbTE hji).
have hd (t : R) : a-f t=(s-t)*:eps i+r*:eps j.
  apply/ffunP=> k; rewrite /a /euclidean_coordinate_line !ffunE.
  change (v k+s*(if k==i then 1 else 0)+r*(if k==j then 1 else 0)-
    (v k+t*(if k==i then 1 else 0))=
    (s-t)*(if k==i then 1 else 0)+r*(if k==j then 1 else 0)).
  ring.
have hmem : metric_closed_ball a r (f s).
  rewrite /metric_closed_ball /= inner_metric_distanceE hd subrr scale0r add0r.
  by rewrite inner_normZ euclidean_coordinate_unit_norm mulr1 ger0_norm // ltW.
split=> //; apply/seteqP; split=> y.
- move=> [[t _ <-] ht].
  have hb : (inner_norm hB (a-f t)<=r)%R := ht.
  have hsqr : inner_norm hB (a-f t)^+2<=r^+2.
    by rewrite (ler_sqr (inner_norm_nonnegative hB (a-f t)) (ltW hr)).
  rewrite inner_norm_sqr hd in hsqr.
  rewrite (@inner_sum_square R _ B hB)
    !(@inner_scale_square R _ B hB) heii hejj
    (bilZl (inner_bilinear hB))
    (bilZr (inner_bilinear hB)) heij /= !scaler0 !mulr1 !addr0 in hsqr.
  have hzero : (s-t)^+2=0.
    apply/eqP; rewrite eq_le sqr_ge0 andbT.
    by lra.
  have hst : s=t by apply/eqP; rewrite -subr_eq0 -sqrf_eq0 hzero.
  by rewrite hst.
- move=> ->; split=> //; by exists s.
Qed.
End Lines.
