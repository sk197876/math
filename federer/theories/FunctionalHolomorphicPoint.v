(** Federer (1969), 3.4.12, p. 339, extending the
    functional equations of 3.4.5, p. 321, and
    the strata of 3.4.8(11), pp. 333–335. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric FiniteCoordinates ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  HolomorphicCoordinateNorm HolomorphicCoordinateNormBounds HolomorphicLinear HolomorphicUP HolomorphicRestriction HolomorphicArithmetic
  NormDifferentialUP NormDifferentialLinear NormDifferentialLocal NormBoundedLinearTopology
  FunctionalHolomorphicSubmanifoldUP FieldScalarCoordinateMaps FieldCoordinateCovectorsIndependent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_holomorphic_point]: the origin is
    an actual zero-dimensional functional holomorphic stratum in every
    original open neighbourhood, extending 3.4.8(11), p. 333,
    under 3.4.12, p. 339. *)
Theorem functional_holomorphic_point (R:realType) n
    (U:set (coordinate_space (ComplexScalars.C R) n)):
  @open (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) U ->
  U 0 ->@is_functional_holomorphic_submanifold R n 0 U [set 0].
Proof.
move=>hU hU0.
pose C:=ComplexScalars.C R.
pose X:=coordinate_space C n.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose CR:=restricted_space (ComplexScalars.embed R) C^o.
pose NX:=@holomorphic_coordinate_norm R n.
pose hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n).
pose NC:=@complex_modulus R;pose hNC:=@complex_modulus_real_norm R.
have hInterior x (hx:U x):@norm_domain_interior R XR NX U x.
  have hOpen:=hU;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R XR NX hNX U x).2 (hOpen x hx).
have hBound i:@norm_bounded_linear R XR CR NX NC (complex_hom_real (@field_scalar_coordinate_map C n i)).
  exists 1;split;first exact:ler01.
  move=>x;rewrite mul1r;exact:holomorphic_coordinate_norm_bound.
rewrite /is_functional_holomorphic_submanifold subn0.
split;first exact:leq0n.
split;first exact:hU.
exists (fun (i:'I_n) (x:X)=>x i),(fun _=>(1:C));split.
- move=>i;exact:(@holomorphic_bounded_linear R X C^o NX NC hNX hNC U
    (@field_scalar_coordinate_map C n i) hInterior (hBound i)).
split;first exact:(@holomorphic_constant R X C^o NX NC hNX hNC U 1 hInterior).
split.
- move=>x;split.
  + move=>->;split;first exact:hU0.
    split;first by move=>i;rewrite ffunE.
    by move/eqP;rewrite oner_eq0.
  + move=>[_ [hCoordinates _]];apply/ffunP=>i;by rewrite ffunE hCoordinates.
- move=>x hx;have hUx:U x by rewrite hx.
  exists (fun i=>@field_scalar_coordinate_map C n i);split.
  + move=>i;exact:(@norm_differential_linear R XR CR NX NC hNX hNC U x
      (complex_hom_real (@field_scalar_coordinate_map C n i)) (hInterior x hUx) (hBound i)).
  + exact:field_coordinate_covectors_independent.
Qed.
