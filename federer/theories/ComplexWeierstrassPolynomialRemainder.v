(** Federer (1969), 3.4.12, p. 339: subtracting the
    original monic preparation polynomial from xi^k gives an
    actual directional polynomial remainder. Use its original difference
    representative, exact finite values and proved local derivative transport. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  NormDifferentialUP NormRegularity NormAnalyticLocal NormAnalyticOperations
  NormHigherDifferentialUP NormHigherDifferentialLocal ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicUP HolomorphicRestriction HolomorphicArithmetic HolomorphicNegation
  HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermUP
  HolomorphicGermOperationsUP HolomorphicGermSealed HolomorphicGermRing
  ComplexWeierstrassPreparationUP ComplexWeierstrassDivisionUP ComplexWeierstrassTransverseUP
  WeierstrassFiniteFamilyExtension ComplexWeierstrassFiniteRemainderVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Remainder.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation KR:=(restricted_space (ComplexScalars.embed R) K).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Variables (NX:XR->R) (NK:KR->R).
Variables (hNX:is_real_norm NX) (hNK:is_real_norm NK).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m XR CR NX N hNX hN).
Local Notation ev:=(fun m=>@ContinuousMultilinear.evaluation R m XR CR NX N hNX hN).
Local Notation ZN:=(fun m=>@ContinuousMultilinear.norm R m XR CR NX N hNX hN).
Local Notation hZ:=(fun m=>@ContinuousMultilinear.laws R m XR CR NX N hNX hN).

(** Source for [complex_weierstrass_polynomial_remainder]: every original
    preparation candidate supplies an actual remainder in division
    of xi^k, extending 3.4.6(2), p. 322, under 3.4.12,
    p. 339. Monic cancellation is a proved local value
    equation; all high derivatives vanish on that same neighbourhood. *)
Theorem complex_weierstrass_polynomial_remainder v (xi:Hom X C^o)
    (inclusion:Hom K X) (projection:Hom X K) k
    (power:@holomorphic_representative_type R X NX hNX 0)
    (W:@holomorphic_germ_ring R X NX hNX 0)
    (Wi:'I_k->@holomorphic_germ_ring R K NK hNK 0):
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  holomorphic_representative_value power=(fun x=>(xi x)^+k) ->
  is_holomorphic hNX hN setT (holomorphic_representative_value power) ->
  @is_complex_weierstrass_polynomial_germ R X K NX NK hNX hNK xi projection k W Wi ->
  @is_complex_directional_polynomial_germ R X NX hNX k v
    ((holomorphic_germ power:@holomorphic_germ_ring R X NX hNX 0)-W).
Proof.
move=>hSplit hPowerValues hPower [w [hRepW [c [_ [_ [U [haU [hw hWValues]]]]]]]].
have [d hD]:=@weierstrass_finite_family_extension (K->C) k
  (fun i=>holomorphic_representative_value (c i)) (fun _=>0).
pose D i x:=-d i (projection x).
pose F:=fun x=>\sum_(i<k) (xi x)^+i*D i (inclusion (projection x)).
have hOpen x (hx:U x):norm_domain_interior NX U x:=
  ((norm_analytic_class_all_orders hw.1 0%N).1 x hx).1.
have hExact x (hx:U x):F x=holomorphic_representative_value power x-holomorphic_representative_value w x.
  rewrite hPowerValues (hWValues x hx) opprD addrA subrr add0r /F -sumrN.
  apply:eq_bigr=>i _;by rewrite /D (complex_weierstrass_transverse_left_inverse hSplit) hD mulrN.
have hPowerU:=@holomorphic_open_restriction R X C^o NX N hNX hN setT U
  (holomorphic_representative_value power) (fun x _=>Logic.I) hOpen hPower.
have hDifference:=holomorphic_add hPowerU (holomorphic_negate hw).
have hF:=@norm_analytic_domain_agreement R XR CR NX N hNX hN U
  (fun x=>holomorphic_representative_value power x-holomorphic_representative_value w x) F
  (fun x hx=>esym (hExact x hx)) hDifference.1.
pose difference:=@holomorphic_add_representatives R X NX hNX 0 power
  (@holomorphic_negate_representative R X NX hNX 0 w).
have hRep:holomorphic_germ difference=(holomorphic_germ power:@holomorphic_germ_ring R X NX hNX 0)-W.
  rewrite -hRepW.
  change (holomorphic_germ difference=@HolomorphicGerms.add R X NX hNX 0 (holomorphic_germ power)
    (@HolomorphicGerms.opp R X NX hNX 0 (holomorphic_germ w))).
  by rewrite (@holomorphic_germ_negate_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX 0))
    (@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX 0)).
exists difference;split;first exact:hRep.
exists U;split;first exact:haU.
split;first exact:hDifference.
move=>m hm x hx z hz.
have hActualF:=(@norm_higher_differential_local_agreement R XR CR NX N hNX hN Z ev ZN hZ
  m setT setT U (holomorphic_representative_value difference) F hOpen
  (fun y _=>iff_refl _) (fun y hy _=>esym (hExact y hy)) x hx z).1 hz.
exact:(@complex_weierstrass_finite_remainder_vanishing R X K NX NK hNX
  v xi inclusion projection k D U hSplit hF m hm x hx z hActualF).
Qed.
End Remainder.
