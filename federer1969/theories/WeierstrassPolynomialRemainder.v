(** Federer (1969), 3.4.6(2), p. 322: subtracting
    an original monic Weierstrass polynomial from xi^k gives
    a genuine directional polynomial remainder. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormClassZeroTopology
  NormAnalyticUP NormAnalyticLocal NormAnalyticOperations NormBoundedLinearTopology
  LocalGermUP LocalGermSealed AnalyticGermRepresentatives AnalyticGermUP AnalyticGermSealed AnalyticGermRing
  WeierstrassPreparationUP WeierstrassDivisionUP WeierstrassTransverseUP WeierstrassFiniteFamilyExtension
  WeierstrassFiniteRemainderVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_polynomial_remainder]: every
    original preparation candidate supplies a valid remainder
    in division of xi^k, supporting uniqueness in
    3.4.6(2), p. 322. The monic terms
    cancel in actual neighbourhood equations; finite translated
    lines prove every required derivative zero. *)
Theorem weierstrass_polynomial_remainder (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K) k
    (power:analytic_representative_type hNX (0:X))
    (W:@analytic_germ_ring R X NX hNX 0) (Wi:'I_k->@analytic_germ_ring R K NK hNK 0):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  analytic_representative_value power=(fun x=>(xi x)^+k) ->
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    setT (analytic_representative_value power) ->
  @is_weierstrass_polynomial_germ R X K NX NK hNX hNK xi projection k W Wi ->
  @is_directional_polynomial_germ R X NX hNX k v
    ((analytic_germ power:@analytic_germ_ring R X NX hNX 0)-W).
Proof.
move=>hSplit hPowerValues hPower [w [hRepW [c [_ [_ [U [haU [hw hWValues]]]]]]]].
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
have [d hD]:=@weierstrass_finite_family_extension (K->R) k
  (fun i=>analytic_representative_value (c i)) (fun _=>0).
pose C i x:=-d i (projection x).
pose F:=fun x=>\sum_(i<k) (xi x)^+i*C i (inclusion (projection x)).
have hOpen x (hx:U x):norm_domain_interior NX U x:=
  ((norm_analytic_class_all_orders hw 0%N).1 x hx).1.
have hExact x (hx:U x):F x=analytic_representative_value power x-analytic_representative_value w x.
  rewrite hPowerValues (hWValues x hx) opprD addrA subrr add0r /F -sumrN.
  apply:eq_bigr=>i _.
  by rewrite /C (weierstrass_transverse_left_inverse hSplit) hD mulrN.
have hPowerU:=@norm_analytic_open_restriction R X R^o NX N hNX hN setT U
  (analytic_representative_value power) (fun x _=>Logic.I) hOpen hPower.
have hDifference:=@norm_analytic_subtract R X R^o NX N hNX hN U
  (analytic_representative_value power) (analytic_representative_value w) hPowerU hw.
have hF:=@norm_analytic_domain_agreement R X R^o NX N hNX hN U
  (fun x=>analytic_representative_value power x-analytic_representative_value w x) F
  (fun x hx=>esym (hExact x hx)) hDifference.
have [g hG]:=@analytic_representative_from_domain R X NX hNX 0 U F (hF 0 haU).
pose difference:=@analytic_add_representatives R X NX hNX 0 power
  (@analytic_negate_representative R X NX hNX 0 w).
have hGerms:analytic_germ g=analytic_germ difference.
  pose TX:=Topological.clone (real_norm_metric_space hNX) _.
  have hGermLaws:=@LocalGerms.laws TX R (@analytic_representative_type R X NX hNX 0)
    (@analytic_representative_value R X NX hNX 0) 0.
  apply/(local_germ_equality hGermLaws).
  exists U;split.
  - exact:(@norm_class_zero_domain_open R X R^o NX N hNX U (analytic_representative_value w)
      (norm_class_continuous (norm_analytic_class_all_orders hw 0%N))).
  - split;first exact:haU.
    move=>x hx;rewrite hG hExact //;reflexivity.
have hRepG:analytic_germ g=(analytic_germ power:@analytic_germ_ring R X NX hNX 0)-W.
  rewrite hGerms -hRepW.
  change (analytic_germ difference=@AnalyticGerms.add R X NX hNX 0 (analytic_germ power)
    (@AnalyticGerms.opp R X NX hNX 0 (analytic_germ w))).
  by rewrite (@analytic_germ_negate_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX 0))
    (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX 0)).
exists g;split;first exact:hRepG.
exists U;split;first exact:haU.
split;first by rewrite hG.
rewrite hG.
exact:(@weierstrass_finite_remainder_vanishing R X K NX NK hNX v xi inclusion projection k C U hSplit hF).
Qed.
