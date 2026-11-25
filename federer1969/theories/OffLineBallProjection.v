(** Federer (1969), 2.9.18(2), p. 163: projection of a Euclidean ball after
    removing a straight line. The projection contains the open coordinate
    interval and is contained in the closed interval. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring num_normedtype.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  InnerMetric EuclideanCoordinateMetric EuclideanPlaneLines EuclideanAffineLineGeometry
  MetricClosedBalls RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Projection.
Variable R : realType.
Variable n : nat.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Variable i j : 'I_n.
Variable v : E.
Local Notation f := (euclidean_coordinate_line i v).
Local Notation T := (euclidean_affine_coordinate_line i v).

(** Source for [off_line_ball_projection_upper]: supporting
    upper inclusion for psi B(x,r)=2r in Federer
    2.9.18(2), p. 163. Every coordinate projection
    of the closed ball lies in its closed scalar interval;
    removing the line only decreases this image. *)
Lemma off_line_ball_projection_upper (s r : R) :
  (fun x : E => x i) @` (metric_closed_ball (f s) r `\` T)
    `<=` `[f s i-r,f s i+r].
Proof.
move=> t [x [hx _] <-].
have h := le_trans (@euclidean_coordinate_nonexpanding R n i (f s) x) hx.
rewrite real_line_metric_distanceE in h.
rewrite /= in_itv /=; apply/andP; split.
- have h1 := le_trans (ler_norm (f s i-x i)) h; lra.
- have h1 := le_trans (ler_norm (x i-f s i)) (ltac:(by rewrite distrC; exact h)); lra.
Qed.

(** Source for [off_line_ball_projection_lower]: supporting
    lower inclusion for psi B(x,r)=2r in Federer
    2.9.18(2), p. 163. A point projecting strictly
    inside the coordinate interval can be moved a positive
    amount in a second coordinate while staying inside the
    Euclidean ball and leaving T. The proof uses the norm
    triangle inequality, with no change of ambient metric. *)
Lemma off_line_ball_projection_lower (s r : R) : j != i ->
  `]f s i-r,f s i+r[ `<=`
    (fun x : E => x i) @` (metric_closed_ball (f s) r `\` T).
Proof.
move=> hji t; rewrite /= in_itv /= => /andP [hl hu].
have hij : i != j by rewrite eq_sym.
have habs : `|f s i-t|<r.
  rewrite ltr_norml; apply/andP; split; lra.
pose h := (r-`|f s i-t|)/2.
have hh : 0<h by rewrite /h; lra.
pose g : E := f (t-v i).
pose z : E := euclidean_coordinate_line j g h.
have hgi : g i=t.
  by rewrite /g euclidean_coordinate_line_value eqxx mulr1 addrC subrK.
have hgj : g j=v j.
  by rewrite /g euclidean_coordinate_line_value (negbTE hji) mulr0 addr0.
have hzi : z i=t.
  by rewrite /z euclidean_coordinate_line_value (negbTE hij) mulr0 addr0 hgi.
have hzj : z j=v j+h.
  by rewrite /z euclidean_coordinate_line_value eqxx mulr1 hgj.
have hnot : ~T z.
  move=> /euclidean_affine_coordinate_line_coordinates hz.
  have he := hz j hji.
  rewrite hzj in he.
  have he0 : h=0 by lra.
  by rewrite he0 ltxx in hh.
have hdg : mdist (f s) g=`|f s i-t|.
  rewrite /g euclidean_coordinate_line_distance real_line_metric_distanceE.
  rewrite euclidean_coordinate_line_value eqxx mulr1.
  congr (Num.norm _); ring.
have hdz : mdist g z=h.
  rewrite inner_metric_distanceE /z /euclidean_coordinate_line opprD addrA subrr add0r inner_normN.
  by rewrite inner_normZ euclidean_coordinate_unit_norm mulr1 ger0_norm // ltW.
exists z; last exact hzi.
split=> //; apply: (le_trans (metric_triangle (f s) g z)).
rewrite hdg hdz; apply: ltW; rewrite /h; lra.
Qed.
End Projection.
