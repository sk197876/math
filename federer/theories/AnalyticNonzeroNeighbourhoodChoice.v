(** Federer (1969), 3.4.8(11), p. 333:
    the full-dimensional regular neighbourhood is an
    actual norm ball outside Phi=0. Choose it
    inside the required open set using the
    proved uniform small-ball component bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology lra.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP NormOpenDomainLaws
  NormBoundedLinearTopology NormAnalyticUP SetGermUP FiniteAnalyticVarietyUP GermVanishingSealed
  AnalyticDepthSealed AnalyticSmallBallComponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NonzeroChoice.
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

(** Source for [analytic_nonzero_neighbourhood_choice]:
    choose the original full-dimensional regular stratum
    inside any prescribed neighbourhood, 3.4.8(11),
    p. 333. The component bound comes from
    the smaller-depth induction, not arbitrary open restriction. *)
Theorem analytic_nonzero_neighbourhood_choice (A:set X) (phi:X->R^o):
  A 0 ->@norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) A phi ->
  (forall U H:set X,U 0 ->@is_finite_analytic_variety R X NX hNX U H ->
    germ H<>germ set0 ->
    (depth (@AnalyticSetIdeal.value R X NX hNX 0 (germ H))<n.+1)%N ->
    exists O:set X,@open T O /\O 0 /\
      finite_set (@connected_component T H @` (H `&` O))) ->
  forall W:set X,@open T W ->W 0 ->
    exists O:set X,@open T O /\O 0 /\O `<=` W /\
      finite_set (@connected_component T (O `&` [set x|phi x<>0]) @`
        (O `&` [set x|phi x<>0])).
Proof.
move=>hA0 hPhi hInduction W hW hW0.
have [r0 [hR0 [hBallA hFinite]]]:=@analytic_small_ball_components_from_lower_depth R n A phi
  hA0 hPhi hInduction.
have hNear:(nbhs (0:T)) W by move:hW;rewrite openE;apply.
have [rho [hRho hBall]]:=(@norm_domain_interior_neighbourhood R X NX hNX W 0).2 hNear.
pose r:=Num.min (rho/2) r0.
have hr:0<r by rewrite /r lt_min;apply/andP;split;[by lra|exact:hR0].
have hRRho:r<=rho/2 by rewrite /r ge_min lexx.
have hRR0:r<=r0 by rewrite /r ge_min lexx orbT.
pose O:set X:=[set x|NX (x-0)<r].
have hO:@open T O.
  rewrite openE=>x hx.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX O x).1
    (@norm_open_ball_domain_interior R X NX hNX 0 r x hx).
have hO0:O 0 by change (is_true (NX (0-0)<r));rewrite subrr (real_seminorm_zero hNX.1).
have hOW:O `<=` W.
  move=>x hx;change (is_true (NX (x-0)<r)) in hx.
  rewrite subr0 in hx.
  have hSmall:NX x<rho by lra.
  have h:=hBall x hSmall;by rewrite add0r in h.
have hEqual:O `&` [set x|phi x<>0] = [set x|NX x<r /\phi x<>0].
  apply/seteqP;split.
  - move=>x [hx hNonzero];split;last exact:hNonzero.
    change (is_true (NX (x-0)<r)) in hx;by rewrite subr0 in hx.
  - move=>x [hx hNonzero];split;last exact:hNonzero.
    change (is_true (NX (x-0)<r));by rewrite subr0.
exists O;split;first exact:hO.
split;first exact:hO0.
split;first exact:hOW.
rewrite hEqual;exact:hFinite r hr hRR0.
Qed.
End NonzeroChoice.
