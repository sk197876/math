(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), pp. 333–335:
    finite holomorphic varieties return from the original
    orthogonal source coordinates by pulling back their
    actual finite equations. This connection applies the
    existing holomorphic composition theorem directly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicLinear HolomorphicFiniteCalculus Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  HolomorphicUP HolomorphicLinear HolomorphicFiniteCalculus FiniteHolomorphicVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_holomorphic_linear_pullback]:
    actual holomorphic boundary varieties are invariant
    under the original source-coordinate change in
    3.4.12, p. 339, extending 3.4.8(11), pp. 333–335. The result
    uses only a bounded linear source map. *)
Theorem finite_holomorphic_linear_pullback (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    (u:Hom X X) (U S:set X):
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) X) NX NX (complex_hom_real u) ->
  @is_finite_holomorphic_variety R X NX hNX U S ->
  @is_finite_holomorphic_variety R X NX hNX (u @^-1` U) (u @^-1` S).
Proof.
move=>hBound [hU [I [f [hF hEquation]]]].
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose A:set X:=u @^-1` U.
have hContinuous:=@norm_bounded_linear_continuous R XR XR NX NX hNX hNX (complex_hom_real u) hBound.
have hA:@open T A:=@open_comp T T u U (fun x _=>hContinuous x) hU.
have hInterior x (hx:A x):@norm_domain_interior R XR NX A x.
  have hOpen:=hA;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R XR NX hNX A x).2 (hOpen x hx).
have hUHolomorphic:=@holomorphic_bounded_linear R X X NX NX hNX hNX A u hInterior hBound.
split;first exact:hA.
exists I,(fun i x=>f i (u x));split.
- move=>i;exact:(@holomorphic_compose_on R X X (ComplexScalars.C R)^o NX NX (@complex_modulus R)
    hNX hNX (@complex_modulus_real_norm R) A U u (f i) (fun x hx=>hx) hUHolomorphic (hF i)).
- move=>x;exact:hEquation (u x).
Qed.
