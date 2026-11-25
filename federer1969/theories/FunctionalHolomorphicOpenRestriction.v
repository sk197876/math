(** Federer (1969), 3.4.12, p. 339, extending the
    functional equations of 3.4.5, p. 321, and
    the strata of 3.4.8(11), pp. 333–335. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric FiniteCoordinates ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  HolomorphicCoordinateNorm HolomorphicCoordinateNormBounds HolomorphicLinear HolomorphicUP HolomorphicRestriction HolomorphicArithmetic
  NormDifferentialUP NormDifferentialLinear NormDifferentialLocal NormBoundedLinearTopology
  FunctionalHolomorphicSubmanifoldUP  .
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_holomorphic_open_restriction]: restrict
    the original functional equations and independent differentials to
    the selected open neighbourhood, extending 3.4.8(11), p. 335,
    under 3.4.12, p. 339. *)
Theorem functional_holomorphic_open_restriction (R:realType) n m
    (U V S:set (coordinate_space (ComplexScalars.C R) n)):
  @is_functional_holomorphic_submanifold R n m U S ->
  @open (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) V ->
  V `<=` U ->@is_functional_holomorphic_submanifold R n m V (V `&` S).
Proof.
move=>[hMN [hU [f [g [hF [hG [hEquation hDifferentials]]]]]]] hV hVU.
pose X:=coordinate_space (ComplexScalars.C R) n.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose CR:=restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o.
pose NX:=@holomorphic_coordinate_norm R n.
pose hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n).
have hInterior x (hx:V x):@norm_domain_interior R XR NX V x.
  have hOpen:=hV;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R XR NX hNX V x).2 (hOpen x hx).
split;first exact:hMN.
split;first exact:hV.
exists f,g;split.
- move=>i;exact:(holomorphic_open_restriction hVU hInterior (hF i)).
split;first exact:(holomorphic_open_restriction hVU hInterior hG).
split.
- move=>x;split.
  + move=>[hx /hEquation [_ hRest]];by split.
  + move=>[hx hRest];split;first exact:hx.
    apply/(hEquation x);split;[exact:hVU x hx|exact:hRest].
- move=>x [hx hSx];have [D [hD hIndependent]]:=hDifferentials x hSx.
  exists D;split;last exact:hIndependent.
  move=>i;exact:(@norm_differential_restrict R XR CR NX (@complex_modulus R)
    U V (f i) x (complex_hom_real (D i)) hVU (hInterior x hx) (hD i)).
Qed.
