(** Federer (1969), 3.4.11, p. 338:
    the entire original leading ideal lies in the
    actual tangent-cone vanishing ideal. The original generator
    family and the opaque least-ideal law prove this
    inclusion without presupposing an analytic tangent cone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermUP AnalyticGermRing
  AnalyticGermRepresentatives SetGermUP GermVanishingUP GermVanishingSealed
  GermVanishingRepresentative GermVanishingIdeal CommutativeIdealUP TangentConeUP
  AnalyticInitialPolynomialGermUP AnalyticInitialIdealSealed AnalyticInitialTangentVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_initial_ideal_tangent_inclusion]:
    the leading ideal is contained in the ideal
    of the actual tangent cone, 3.4.11, p. 338.
    This statement uses only original set germs and
    their independently specified vanishing ideals. *)
Theorem analytic_initial_ideal_tangent_inclusion (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (S:set X):
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  let I:=@AnalyticSetIdeal.value R X NX hNX 0 (@set_germ T 0 S) in
  @AnalyticInitialIdeal.value R X NX hNX I `<=`
    @AnalyticSetIdeal.value R X NX hNX 0 (@set_germ T 0 (norm_tangent_cone NX S 0)).
Proof.
move=>T I.
apply:(generated_commutative_ideal_minimal (@AnalyticInitialIdeal.laws R X NX hNX I)
  (@analytic_set_ideal_ring_laws R X NX hNX 0 (@set_germ T 0 (norm_tangent_cone NX S 0)))).
move=>beta [alpha [hAlpha [k [P [f [hInitial [hValues <-]]]]]]].
apply/(@analytic_set_ideal_representative_equation R X NX hNX 0 f (norm_tangent_cone NX S 0)).
exists setT;split;first exact:openT.
split;first done.
move=>v hTangent _;rewrite hValues.
exact:(@analytic_initial_polynomial_tangent_vanishes R X NX hNX S alpha k P hAlpha hInitial v hTangent).
Qed.
