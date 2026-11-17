(** Federer (1969), 3.4.8(11), p. 333:
    the full-dimensional ball complement has finitely
    many components. Its actual critical variety has
    strictly smaller depth. The induction input concerns
    only those smaller-dimensional analytic germs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanCoordinateMetric EuclideanStiefelInnerSplitting
  InnerNorm HilbertFormCompactness NormDifferentialUP NormDifferentialDirectional NormOpenDomainLaws
  NormLinearDomainLaws NormConvexConnected NormAnalyticUP NormAnalyticLocal NormAnalyticOperations
  SetGermUP FiniteAnalyticVarietyUP GermVanishingSealed AnalyticDepthSealed AnalyticComponentBarrier
  AnalyticNonconstantLocal AnalyticCriticalVariety AnalyticCriticalLocalInduction AnalyticBallComplementComponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section BallInduction.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n.+1).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n.+1)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n.+1)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@AnalyticDepth.value R X (@euclidean_inner_product R n.+1)
  (@euclidean_inner_productP R n.+1) n.+1 (@coordinate_basis R n.+1) (@coordinate_basisP R n.+1)
  (dual_basis (@coordinate_basisP R n.+1))).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).

(** Source for [analytic_ball_components_from_lower_depth]:
    discharge the critical-set component input in the
    original full-dimensional case of 3.4.8(11),
    p. 333. A sphere point and an actual
    positive interior value prove that the original
    barrier is nowhere locally constant. The empty
    complement is treated separately. *)
Theorem analytic_ball_components_from_lower_depth (phi:X->R^o) (rho epsilon:R):
  0<epsilon ->epsilon<rho ->
  @norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R)
    [set x|NX x<rho] phi ->
  (forall W L:set X,W 0 ->@is_finite_analytic_variety R X NX hNX W L ->
    germ L<>germ set0 ->(depth (ideal (germ L))<n.+1)%N ->
    exists U:set X,@open T U /\U 0 /\
      finite_set (@connected_component T L @` (L `&` U))) ->
  finite_set (@connected_component T [set x|NX x<epsilon /\phi x<>0] @`
    [set x|NX x<epsilon /\phi x<>0]).
Proof.
move=>hE hER hPhi hInduction.
pose A:set X:=[set x|NX x<rho].
pose S:set X:=[set x|NX x<epsilon /\phi x<>0].
case:(pselect (exists b,S b))=>[[b hSb]|hEmpty].
- pose psi:X->R^o:=fun y=>(epsilon^+2-(NX y)^+2)*(phi y)^+2.
  pose c:X:=epsilon *: (@coordinate_basis R n.+1 ord0).
  have hNc:NX c = epsilon.
    by rewrite /c inner_normZ euclidean_coordinate_unit_norm mulr1 (ger0_norm (ltW hE)).
  have hAb:A b:=lt_trans hSb.1 hER.
  have hAc:A c by change (is_true (NX c<rho));rewrite hNc.
  have hPsi:=@analytic_component_barrier_analytic R n.+1 A phi epsilon hPhi.
  have hPositive:0<psi b:=@analytic_component_barrier_positive R n.+1 phi epsilon b hE hSb.1 hSb.2.
  have hZero:psi c = 0:=@analytic_component_barrier_sphere_zero R n.+1 phi epsilon c hNc.
  have hDifferent:psi b<>psi c by move=>h;move:hPositive;rewrite h hZero ltxx.
  have hConnected:@connected (real_norm_metric_space hNX) A.
    have hEqual:A = [set x|NX (x-0)<rho].
      apply:funext=>x;change (is_true (NX x<rho) = is_true (NX (x-0)<rho));by rewrite subr0.
    rewrite hEqual;exact:(@norm_inner_convex_connected R X NX hNX [set x|NX (x-0)<rho]
      (@norm_open_ball_convex R X NX hNX 0 rho)).
  have hNotConstant:=@analytic_nonconstant_nowhere_locally_constant R X NX hNX A psi b c
    hConnected hPsi hAb hAc hDifferent.
  have [D0 [F [hD0 [hF [hEquation hVariety]]]]]:=
    @analytic_critical_variety_exists R X NX hNX n.+1 (@coordinate_basis R n.+1)
      (@coordinate_basisP R n.+1) A psi hPsi.
  apply:(@analytic_ball_complement_components_from_induction R n.+1 A phi epsilon
    (ltn0Sn n) hE hPhi _).
  + move=>x hx;exact:le_lt_trans hx hER.
  + move=>D hD a ha.
    have hSame:[set x|A x /\forall v,D x v = 0] = [set x|A x /\forall v,D0 x v = 0].
      apply/seteqP;split.
      * move=>x [hx hZeroD];split;first exact:hx.
        have hOperators:=norm_differential_unique hNX (@scalar_absolute_value_norm R)
          (hD x hx) (hD0 x hx).
        by move=>v;rewrite -hOperators hZeroD.
      * move=>x [hx hZeroD];split;first exact:hx.
        have hOperators:=norm_differential_unique hNX (@scalar_absolute_value_norm R)
          (hD x hx) (hD0 x hx).
        by move=>v;rewrite hOperators hZeroD.
    rewrite hSame.
    have hDual i j:dual_basis (@coordinate_basisP R n.+1) i (@coordinate_basis R n.+1 j) =
        if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
    exact:(@analytic_critical_local_finiteness_from_induction R X (@euclidean_inner_product R n.+1)
      (@euclidean_inner_productP R n.+1) n (@coordinate_basis R n.+1) (@coordinate_basisP R n.+1)
      (@euclidean_coordinate_orthonormal_family R n.+1) (dual_basis (@coordinate_basisP R n.+1))
      hDual A psi D0 hVariety hD0 (fun a _=>hNotConstant a) hInduction a (le_lt_trans ha hER)).
- have hS:S = set0.
    apply/seteqP;split.
    + move=>x hx;exfalso;apply:hEmpty;by exists x.
    + by move=>x.
  change (finite_set (@connected_component T S @` S)).
  rewrite hS image_set0;exact:finite_set0.
Qed.
End BallInduction.
