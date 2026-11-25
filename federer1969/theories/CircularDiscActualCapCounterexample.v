(** Federer (1969), 3.3.19, p. 305: the
    auxiliary strict-radius defect occurs at actual
    original parents at every positive level. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct InnerProductUP Bilinear InnerNorm InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws CircularTrigonometryUP CircularTrigonometrySealed
  CircularUnitVectors CircularDiscCaps CircularCapStrictRadiusCounterexample CircularDiscTreeUP CircularDiscLimitUP
  CircularDiscFixedBoundaryPoint StructureCone StructureConeBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Actual.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 2)).
Local Notation B:=(@euclidean_inner_product R 2).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation u:=(@circular_unit_vector R 0).
Local Notation xi:=(@circular_unit_vector R (2*(p/6))).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_actual_cap_counterexample]: at
    EVERY actual parent level j>=1, the original endpoint
    a= exp(0i) and an actual original parent have a
    closed-cap point at exact excluded cone radius rho_j.
    It is below 1-2/(j+4) in the original normalized
    radial coordinate, hence outside the printed second
    cap. This proves the p. 305 auxiliary inclusion
    needs strict-aperture/radius buffering even for actual
    original A-points and arbitrarily late original parents. *)
Theorem circular_disc_actual_cap_counterexample j:(1<=j)%N ->
  exists z x:E,z \in H j /\A u /\metric_closed_ball z (rho j) u /\
    circular_disc_cap z (rho j) (@circular_unit_vector R (p/6)) (p/6) x /\
    B (x-z) u<(rho j)*(1-2/(j+4)%:R) /\
    (forall b:R,C b= 1-2/(j+4)%:R ->~circular_disc_cap z (rho j) u b x) /\
    forall V:G (R_n R 2) 1,~structure_cone V u (rho j)%:E (1/2) x.
Proof.
move=>hj.
have [z [hz hPoint]]:= @circular_disc_fixed_boundary_branch R H hH j.
have ha:= @circular_disc_fixed_boundary_point_in_limit R H hH A hA.
pose r:= rho j.
have hr:0<r:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
  (@FactorialDiscScales.laws R) j.
pose x:= z+r*:xi.
have hX:x-z= r*:xi by rewrite /x addrAC subrr add0r.
have hU:u-z= r*:u by rewrite {1}hPoint addrAC subrr add0r.
have hABall:metric_closed_ball z r u.
  change (is_true (mdist z u<=r)).
  by rewrite metric_sym inner_metric_distanceE hU inner_normZ circular_unit_vector_norm mulr1 (ger0_norm (ltW hr)).
have hXBall:metric_closed_ball z r x.
  change (is_true (mdist z x<=r)).
  by rewrite metric_sym inner_metric_distanceE hX inner_normZ circular_unit_vector_norm mulr1 (ger0_norm (ltW hr)).
have hJ5:(5<=j+4)%N.
  change (is_true (1+4<=j+4)%N);by rewrite leq_add2r.
have [_ [hBase _]]:= @circular_cap_strict_radius_counterexample R (j+4)%N hJ5.
rewrite subr0 in hBase.
have hBelow:B (x-z) u<r*(1-2/(j+4)%:R).
  rewrite hX (bilZl (inner_bilinear (@euclidean_inner_productP R 2))).
  change (is_true (r* B xi u<r*(1-2/(j+4)%:R))).
  by rewrite ltr_pM2l.
have hCap:circular_disc_cap z r (@circular_unit_vector R (p/6)) (p/6) x.
  split=>//.
  change (is_true (r* C (p/6)<=B (x-z) (@circular_unit_vector R (p/6)))).
  rewrite hX (bilZl (inner_bilinear (@euclidean_inner_productP R 2))) circular_unit_vector_inner.
  have hAngle:2*(p/6)-p/6= p/6 by ring.
  change (is_true (r* C (p/6)<=r* C (2*(p/6)-p/6)));by rewrite hAngle.
have hDistance:mdist x u= r.
  have hVector:x-u= r*:(xi-u).
    rewrite {1}hPoint /x opprD (addrACA z (r*:xi) (-z) (-(r*:u))) subrr add0r.
    by rewrite scalerBr.
  rewrite inner_metric_distanceE hVector inner_normZ (ger0_norm (ltW hr))
    -inner_metric_distanceE circular_cap_boundary_chord_one mulr1;by [].
exists z,x;split=>//;split=>//;split=>//;split=>//;split=>//;split.
- move=>b hB [_ hCoordinate].
  rewrite hB in hCoordinate.
  have hFalse:= lt_le_trans hBelow hCoordinate;by rewrite ltxx in hFalse.
- move=>V hCone.
  have hRadius:= @structure_cone_norm_bound R 2 1 V u x r%:E (1/2) hCone.
  by rewrite -inner_metric_distanceE hDistance ltxx in hRadius.
Qed.
End Actual.
