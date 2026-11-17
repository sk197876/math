(** Federer (1969), 3.4.12, p. 339, extending 3.4.5,
    p. 321: every finite-dimensional holomorphic variety germ
    has its original unique finite maximal irreducible decomposition.
    The actual Noetherian theorem discharges the conditional premise
    of the already proved component assembly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP NormMetric LinearBasis SetGermUP SetGermOrder
  CommutativeIdealUP HolomorphicGermRing HolomorphicGermNoetherian HolomorphicGermVanishingSealed
  HolomorphicVarietyGermUP HolomorphicIrreducibleComponentsSealed HolomorphicIrreducibleGermCoverUP
  NoetherianHolomorphicIrreducibleComponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_holomorphic_irreducible_component_decomposition]:
    the complete finite-dimensional component assertion, 3.4.12,
    p. 339, at every original centre, including dimension zero.
    Empty germs receive the empty family; all actual ideals and
    maximality are retained. No Noetherianity or decomposition
    conclusion is supplied as an additional premise. *)
Theorem finite_holomorphic_irreducible_component_decomposition (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    n (e:'I_n->X) (he:is_basis e) a
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space (complex_norm_real hNX)) _) a):
  @is_holomorphic_variety_germ R X NX (complex_norm_real hNX) a alpha ->
  finite_set (@HolomorphicIrreducibleComponents.value R X NX (complex_norm_real hNX) a alpha) /\
  (exists K,@is_finite_irreducible_holomorphic_germ_cover R X NX (complex_norm_real hNX) a alpha K /\
    @HolomorphicIrreducibleComponents.value R X NX (complex_norm_real hNX) a alpha=[set beta|beta \in K]) /\
  (forall beta gamma,@HolomorphicIrreducibleComponents.value R X NX (complex_norm_real hNX) a alpha beta ->
    @HolomorphicIrreducibleComponents.value R X NX (complex_norm_real hNX) a alpha gamma ->
    set_germ_subset beta gamma ->beta=gamma) /\
  @HolomorphicSetIdeal.value R X NX (complex_norm_real hNX) a alpha=
    \bigcap_(beta in @HolomorphicIrreducibleComponents.value R X NX (complex_norm_real hNX) a alpha)
      @HolomorphicSetIdeal.value R X NX (complex_norm_real hNX) a beta.
Proof.
move=>hAlpha.
apply:(@noetherian_holomorphic_irreducible_component_decomposition R X NX (complex_norm_real hNX) a alpha _ hAlpha).
exact:(@finite_holomorphic_germ_ring_noetherian R X NX hNX n e a he).
Qed.
