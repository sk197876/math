(** Federer (1969), 3.3.19, p. 305: a boundary
    counterexample to the printed auxiliary closed-cap inclusion
    in the strict-radius cone of 3.3.1, p. 287. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct InnerNorm InnerMetric
  MetricClosedBalls CircularUnitVectors CircularChordLengths CircularSineOrder
  CircularTrigonometryUP CircularTrigonometrySealed RealTrigonometryUP CircularDiscCaps
  StructureCone StructureConeBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Counterexample.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation u:=(@circular_unit_vector R 0).
Local Notation x:=(@circular_unit_vector R (2*(p/6))).

(** Source for [circular_cap_boundary_chord_one]: the actual
    point exp(i pi/3) has distance one from exp(0i).
    This supporting computation makes the strict-radius defect
    in the auxiliary display of 3.3.19, p. 305 explicit. *)
Lemma circular_cap_boundary_chord_one:mdist x u= 1.
Proof.
have hp:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
have h0:0<=p/6 by lra.
have hPi:p/6<=p by lra.
have h:= @circular_unit_chord_length R 0 (p/6) h0 hPi.
by rewrite add0r circular_sine_twelfth_turn in h;rewrite h;field.
Qed.

(** Source for [circular_cap_strict_radius_counterexample]:
    in the unit parent, a= exp(0i), alpha= pi/6 and
    s= 1/2, the actual x= exp(i pi/3) belongs to the
    first printed closed cap and lies below every original
    second-cap threshold 1-2/n, n>=5, but belongs to
    no X(a,2rs,V,s) because its radius is exactly 2rs= 1.
    This qualifies the auxiliary inclusion on p. 305;
    the numbered example's density claims are unchanged. *)
Theorem circular_cap_strict_radius_counterexample n:
  (5<=n)%N ->
  circular_disc_cap (0:E) 1 (@circular_unit_vector R (p/6)) (p/6) x /\
  euclidean_inner_product (x-0) u<1-2/(n%:R:R) /\
  forall V:G (R_n R 2) 1,~structure_cone V u ((1:R)%:E) (1/2) x.
Proof.
move=>hn.
have hProduct:euclidean_inner_product (x-0) u= C (2*(p/6)).
  by rewrite subr0 circular_unit_vector_inner subr0.
have hCos:C (2*(p/6))= 1/2.
  have hAngle:2*(p/6)= p/6+p/6 by ring.
  rewrite hAngle (circular_trig_cosine_add (@CircularTrigonometry.laws R)).
  have hUnit:= circular_trig_unit (@CircularTrigonometry.laws R) (p/6).
  rewrite circular_sine_twelfth_turn in hUnit.
  rewrite circular_sine_twelfth_turn;nra.
have hNat:(5<=n%:R:>R) by rewrite ler_nat.
have hNP:0<(n%:R:R) by lra.
have hInverse:0<(n%:R:R)^-1 by rewrite invr_gt0.
have hNN:(n%:R:R)!=0 by rewrite gt_eqF.
have hCompare:= ler_wpM2r (ltW hInverse) hNat.
rewrite mulfV // in hCompare.
split.
- split.
  + change (is_true (mdist (0:E) x<=1)).
    by rewrite metric_sym inner_metric_distanceE subr0 circular_unit_vector_norm.
  + change (is_true (1*C (p/6)<=euclidean_inner_product (x-0) (@circular_unit_vector R (p/6)))).
    rewrite subr0 circular_unit_vector_inner mul1r.
    have hAngle:2*(p/6)-p/6= p/6 by ring.
    by rewrite hAngle.
- split;first by rewrite hProduct hCos;lra.
  move=>V hCone.
  have hRadius:= @structure_cone_norm_bound R 2 1 V u x ((1:R)%:E) (1/2) hCone.
  by rewrite -inner_metric_distanceE circular_cap_boundary_chord_one ltxx in hRadius.
Qed.
End Counterexample.
