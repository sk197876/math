(** Federer (1969), 3.2.33, p. 270: prove the
    existence of the independently specified positive interval bump.
    The existing opaque flat exponential supplies a local witness. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring.
From Federer Require Import Hom ScalarCoefficients TensorUP RealNormUP NormDifferentialUP NormBoundedBilinearUP
  ContinuousMultilinearUP ContinuousMultilinearSealed NormRegularity NormRegularityOperations
  NormClassInfinityQuadratic FlatExponentialUP FlatExponentialSealed FlatExponentialOrder
  FlatExponentialSmooth PositiveUnitIntervalBumpUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_unit_interval_bump_exists]: supporting
    existence of phi in Federer 3.2.33, p. 270.
    Use the already sealed flat exponential at t(1-t).
    Its branch laws give the exact positive set and zero
    complement; continuous polynomial calculus and the actual
    higher chain rule prove global smoothness. No new globally
    chosen function or private construction import is introduced. *)
Theorem positive_unit_interval_bump_exists (R:realType):
  exists phi:R->R,is_positive_unit_interval_bump phi.
Proof.
pose hN:=@scalar_absolute_value_norm R.
pose N:=fun t:R^o=>`|t|.
pose Z i:=@ContinuousMultilinear.space R i R^o R^o N N hN hN.
pose ev i:=@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN.
pose ZN i:=@ContinuousMultilinear.norm R i R^o R^o N N hN hN.
have hZ i:is_continuous_multilinear_space N N (ev i) (ZN i).
  exact:ContinuousMultilinear.laws.
pose q t:R:=t*(1-t).
pose phi t:R:=@FlatExponential.value R (q t).
have hopen x (_:True):norm_domain_interior N (fun _=>True) x.
  exists 1; split; first exact:ltr01; by move=>v hv.
have hB:norm_bounded_bilinear N N N (fun s t:R^o=>s*t).
  split; first exact:scalar_bilinear.
  exists 1; split; first exact:ler01.
  move=>s t; change (is_true (`|s*t|<= 1*(`|s|*`|t|))); by rewrite normrM mul1r.
have hQuad:=@norm_class_infinity_quadratic R R^o R^o N N hN hN
  Z ev ZN hZ (fun _=>True) (fun s t:R^o=>s*t) hopen hB.
pose Id:=hom_of_linear (linear_id R^o).
have hIdBound:norm_bounded_linear N N Id.
  exists 1; split; first exact:ler01.
  by move=>t; rewrite /Id hom_of_linearE /= mul1r.
have hFlat:=@flat_exponential_class_infinity R Z ev ZN hZ.
have hSmooth:norm_class_all_orders hN hN (fun _=>True) phi.
  move=>k.
  have hId:=@norm_class_linear R R^o R^o N N hN hN (fun _=>True) Id k hopen hIdBound.
  have hMinus:=@norm_class_scale R R^o R^o N N hN hN (fun _=>True)
    (fun t:R^o=>t*t) (-1:R) k (hQuad k).
  have hSum:=@norm_class_add R R^o R^o N N hN hN (fun _=>True) Id
    (fun t:R^o=>(-1:R)*:(t*t)) k hId hMinus.
  have hQ:norm_class hN hN (fun _=>True) q k.
    apply:(@norm_class_domain_agreement R R^o R^o N N hN hN (fun _=>True)
      (fun t:R^o=>Id t+(-1:R)*:(t*t)) q k _ hSum)=>t _.
    change (t+(-1)*(t*t)= t*(1-t)); ring.
  have hComp:=@norm_class_composition R R^o R^o R^o N N N hN hN hN
    (fun _=>True) (fun _=>True) q (@FlatExponential.value R) k hQ (hFlat k).
  apply:(@norm_class_open_restriction R R^o R^o N N hN hN
    (fun _=>True /\ True) (fun _=>True) phi k _ hopen hComp).
  by move=>t _; split.
exists phi; constructor.
- move=>t; apply/andP; split; first exact:flat_exponential_nonnegative.
  exact:flat_exponential_unit_bound.
- move=>t; rewrite /phi flat_exponential_positive /q.
  apply/idP/andP.
  + move=>h; split; nra.
  + move=>[h0 h1]; apply:mulr_gt0 h0 _; by rewrite subr_gt0.
- move=>t ht; apply:(flat_exponential_nonpositive_value (@FlatExponential.laws R)).
  rewrite /q; case:ht=>h; nra.
- exact hSmooth.
Qed.
