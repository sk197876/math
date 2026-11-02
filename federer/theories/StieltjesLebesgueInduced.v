(** Federer (1969), 2.5.17, p. 111: "For example, if g(x) = x for all x in
    R, then mu is the Riemann integral, and psi^+ is the 1 dimensional
    Lebesgue measure L^1 over R; this is the Borel regular measure
    characterized by the property that b - a = L^1{x : a <= x <= b} whenever
    -oo < a < b < oo." For every pair psi^+, psi^- induced by the identity
    map, psi^- = 0 because the identity is nondecreasing, psi^+ is Borel
    regular, and the segment identity at the points of continuity gives
    psi^+{x : a <= x <= b} = b - a. The characterisation of L^1 in
    LebesgueLineUP.v then identifies psi^+ with the sealed measure L^1 of
    LebesgueScalarMeasure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength MeasureUP
  MeasureBasic RadonMeasureUP BorelRegularMeasureUP FunctionLatticeRegularityUP
  RealIntegralFunctionalUP MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP
  CompactSupportFunctionUP StieltjesSums StieltjesIntegral StieltjesDaniellIntegral
  StieltjesMonotone StieltjesImageMeasures LebesgueLineUP LebesgueScalarMeasure
  StieltjesInducedPairLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section IdentityIntegrator.
Variable R : realType.

(** Source for [identity_nondecreasing]: the function g(x) = x of the
    example in Federer 2.5.17, p. 111, is nondecreasing. Supporting
    lemma. *)
Lemma identity_nondecreasing : forall x y : R, x <= y -> (fun t : R => t) x <= (fun t : R => t) y.
Proof. by []. Qed.

(** Source for [identity_locally_finite_variation]: g(x) = x has finite
    variation on every segment, so that it induces measures in the sense
    of Federer 2.5.17, p. 111. Supporting lemma. *)
Lemma identity_locally_finite_variation :
  curve_locally_finite_variation ((fun t : R => t) : R -> real_line_metric R).
Proof. exact: (monotone_locally_finite_variation identity_nondecreasing). Qed.

(** Source for [identity_induced_lebesgue]: "if g(x) = x for all x in R,
    then ... psi^+ is the 1 dimensional Lebesgue measure L^1 over R",
    Federer 2.5.17, p. 111. Direct formalisation for every pair induced
    by the identity map: psi^+ is the sealed measure L^1 and psi^- is
    the zero set function. *)
Theorem identity_induced_lebesgue (psip psim : set R -> \bar R) :
  is_induced_measure_pair (fun t : R => t) psip psim ->
  psip = @lebesgue_scalar_measure R /\ psim = (fun _ => 0%E).
Proof.
move=> hpair.
have [hzero _] := induced_measure_pair_monotone identity_locally_finite_variation
  identity_nondecreasing hpair.
have [hm [_ [_ [_ [hb [_ [_ [_ [_ [_ [hpoint [hincr _]]]]]]]]]]]] :=
  induced_measure_pair_laws identity_locally_finite_variation hpair.
have hc : forall x : R, (fun t : R => t) @ x --> (fun t : R => t) x by move=> x; exact: cvg_id.
have hseg : forall a b : R, a <= b -> psip `[a, b] = (b - a)%:E.
  move=> a b; rewrite le_eqVlt => /orP[/eqP <-|hab].
  - have -> : `[a, a] = [set a].
      apply/seteqP; split=> y; rewrite /= in_itv /=; last by move=> ->; rewrite lexx.
      by move=> /andP[h1 h2]; apply/le_anti; rewrite h1 h2.
    by rewrite (hpoint a (hc a)).1 subrr.
  have [_ h] := hincr a b hab (hc a) (hc b).
  by rewrite h hzero sube0.
have hL : is_lebesgue_line_measure psip by constructor.
split=> //.
exact: lebesgue_line_unique hL (lebesgue_scalar_specification R).
Qed.

(** Source for [lebesgue_identity_induced]: the 1 dimensional Lebesgue
    measure L^1 and the zero measure are the measures psi^+ and psi^-
    induced by g(x) = x, Federer 2.5.17, p. 111. Direct formalisation of
    the converse reading; existence of an induced pair is
    [induced_measure_pair_exists]. *)
Theorem lebesgue_identity_induced :
  is_induced_measure_pair (fun t : R => t) (@lebesgue_scalar_measure R) (fun _ => 0%E).
Proof.
have [psip [psim hpair]] := induced_measure_pair_exists identity_locally_finite_variation.
have [hp hn] := identity_induced_lebesgue hpair.
by rewrite -hp -hn.
Qed.

End IdentityIntegrator.
