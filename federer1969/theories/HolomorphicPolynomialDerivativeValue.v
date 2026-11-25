(** Federer (1969), 3.4.12, p. 339: the actual transverse
    polynomial differential determines the original formal derivative
    function. Compare the existing finite polynomial formula with
    the original differential, using ordinary uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  ComplexModulus ComplexScalarNorm NormDifferentialUP NormDifferentialDirectional
  HolomorphicUP HolomorphicLinear ActualHolomorphicPolynomialTransverseDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Value.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Local Notation C:=(ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Variables (NX:X->R) (NY:Y->R).
Variables (hNX:@is_real_norm R XR NX) (hNY:@is_real_norm R YR NY).
Variables (U:set Y) (P:Hom X Y) (xi:Hom X C^o).
Variable N:nat.
Variable b:'I_N->Y->C.
Variables w wD:X->C.
Variable v:X.
(** Source for [holomorphic_polynomial_actual_derivative_value]:
    W' has its actual formal derivative expression in the
    original coordinates, 3.4.12, p. 339, extending 3.4.8(10),
    pp. 330–331. The original direction has prefix zero and
    coordinate one. No formal derivative value is assumed. *)
Theorem holomorphic_polynomial_actual_derivative_value:
  (forall y,U y ->@norm_domain_interior R YR NY U y) ->
  @norm_bounded_linear R XR YR NX NY (complex_hom_real P) ->
  @norm_bounded_linear R XR CR NX (@complex_modulus R) (complex_hom_real xi) ->
  (forall i,@is_holomorphic R Y C^o NY (@complex_modulus R) hNY
    (@complex_modulus_real_norm R) U (b i)) ->
  (forall x,w x=\sum_(i<N) b i (P x)*(xi x)^+(i:nat)) ->
  P v=0 ->xi v = 1 ->
  (forall a,U (P a) ->exists L:Hom XR CR,
    @has_norm_differential R XR CR NX (@complex_modulus R) (fun x=>U (P x)) w a L /\
    forall u,P u=0 ->L u=wD a*xi u) ->
  forall a,U (P a) ->wD a=\sum_(i<N) (i:nat)%:R*b i (P a)*(xi a)^+(i:nat).-1.
Proof.
move=>hU hP hXi hB hValues hV hXiV hW a ha.
have [L [hL hDirections]]:=@hW a ha.
have [M [hM hMDirections]]:=@actual_holomorphic_polynomial_transverse_differential
  R X Y NX NY hNX hNY U P xi N b w hU hP hXi hB hValues a ha.
have hEqual:=norm_differential_unique hNX (@complex_modulus_real_norm R) hL hM.
have hValue:=hMDirections v hV.
by rewrite -hEqual (hDirections v hV) hXiV !mulr1 in hValue.
Qed.
End Value.
