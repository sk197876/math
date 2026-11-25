(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, pp. 320–321:
    finite analytic equations restrict to actual open subsets,
    supporting the equivalence of the germ and cover definitions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormAnalyticUP NormAnalyticLocal HolomorphicRestriction FiniteHolomorphicVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_holomorphic_variety_open_restriction]:
    a finite analytic variety restricts to a finite analytic
    variety in any actual open subdomain, 3.4.5, pp. 320–321. *)
Lemma finite_holomorphic_variety_open_restriction (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (U V S:set X):
  is_finite_holomorphic_variety hNX U S ->@open (real_norm_metric_space hNX) V ->
  V `<=` U ->is_finite_holomorphic_variety hNX V (V `&` S).
Proof.
move=>[hU [I [f [hf hS]]]] hV hVU.
have hOpen x (hx:V x):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX V x.
  have hNeighbourhood:=hV;rewrite openE in hNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R (restricted_space (ComplexScalars.embed R) X) NX hNX V x).2 (hNeighbourhood x hx)).
split;first exact:hV.
exists I,f;split.
- move=>i;exact (@holomorphic_open_restriction R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX
    (@complex_modulus_real_norm R) U V (f i) hVU hOpen (hf i)).
- move=>x;split.
  + move=>[hx /hS [_ hZero]];by split.
  + move=>[hx hZero];split;first exact:hx.
    apply/(hS x);split;[exact:hVU x hx|exact:hZero].
Qed.
