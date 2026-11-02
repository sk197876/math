(** Federer (1969), 2.7.16, printed p. 139, example (6): "Since the
    orthogonal group O(n) is a compact subset of Hom(R^n, R^n), there exists
    a unique left and right Haar measure theta_n over O(n) such that
    theta_n[O(n)] = 1." Federer gives no proof. The assertion holds for
    every compact group G satisfying the standing hypothesis of 2.7.1, p.
    121, and this module proves it in that generality; the orthogonal group
    is treated in OrthogonalGroupHaarMeasure.v. A Haar measure is the K(G)
    regular measure associated with a left or right Haar integral (2.7.2, p.
    122; HaarIntegralUP.v). The proof supplied here combines the following
    facts. If phi represents the Daniell integral lambda on K(G) and G is
    compact, then the constant function 1 belongs to K(G) and phi(G) =
    lambda(1) (2.4.5, p. 83, and 2.5.13, p. 106). A positive multiple of a
    left Haar integral is a left Haar integral (2.5.2, p. 92, and 2.5.5, p.
    96). A Haar measure of a compact group has finite positive total
    measure, and the left and right Haar measures coincide (2.7.12, p. 129;
    2.7.17, p. 141, CompactGroupNonmeasurable.v). Two left Haar integrals
    differ by a positive factor (2.7.7, p. 125), which equals 1 when both
    give the constant function 1 the value 1, and a K(G) regular measure is
    determined by the integral it represents (2.5.3, p. 94). The local
    erratum has no entry for p. 139. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP MonotoneDaniellIntegralUP
  CompactSupportFunctionUP CompactSupportFunctionLattice FunctionLatticeRegularityUP
  FunctionLatticeRegularUniqueness RealIntegralFunctionalUP MeasureUP MeasureSplit
  MeasureIntegralUniqueness CharacteristicFunctionUP MeasureCharacteristicIntegral
  ExtendedPositiveWeightLimit DaniellSpaceWeakTopology DaniellSpaceCompactSpace
  TopologicalGroupUP TopologicalGroupLaws CovariantIntegralUP HaarIntegralUP HaarIntegralLaws
  HaarIntegralExistence HaarIntegralUniqueness CompactGroupNonmeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactTotal.
Variable R : realType.
Variable X : topologicalType.
Hypothesis hc : compact [set: X].
Local Notation K := (@compactly_supported_continuous_functions R X).

(** Source for [compact_representing_measure_total]: phi(X) is the
    integral of the constant function 1 over the compact space X,
    Federer 2.4.5, p. 83 (the integral of a characteristic function),
    used for the normalisation theta_n[O(n)] = 1 of 2.7.16, p. 139.
    Supporting lemma: if phi represents lambda on K(X), then
    phi(X) = lambda(1). *)
Lemma compact_representing_measure_total (phi : set X -> \bar R) (lambda : (X -> R) -> R) :
  is_measure phi -> is_real_integral_functional phi K lambda ->
  phi [set: X] = (lambda (fun _ => 1))%:E.
Proof.
move=> hm hrep.
have hchar : is_characteristic_function [set: X] (fun _ : X => (1 : R)).
  by constructor=> [x _ //|x hx]; exfalso; exact: hx I.
have hi := measure_characteristic_integral hm hchar (measure_measurable_whole hm).
have hj := hrep _ (compact_space_constant_one R hc).
exact: (measure_integral_unique hi hj).
Qed.

End CompactTotal.

Section HaarScaling.
Variable R : realType.
Variable G : Type.
Variable X : topologicalType.
Variable A : G -> X -> X.
Local Notation K := (@compactly_supported_continuous_functions R X).

(** Source for [nonzero_invariant_integral_scale]: a positive multiple
    c lambda of a nonzero monotone invariant integral lambda is one,
    Federer 2.5.2, p. 92, 2.5.5, p. 96, and 2.7.2, p. 122; supporting
    the normalisation theta_n[O(n)] = 1 of 2.7.16, p. 139. Supporting
    lemma. *)
Lemma nonzero_invariant_integral_scale (c : R) (lambda : (X -> R) -> R) :
  0 < c -> is_nonzero_monotone_invariant_integral A lambda ->
  is_nonzero_monotone_invariant_integral A (fun u => c * lambda u).
Proof.
move=> hc [[hD hlaw] hM [u hu hu0]]; split.
- split; first exact: (daniell_integrals_scale_nonnegative (ltW hc) hD).
  by move=> v g hv; rewrite (hlaw v g hv) !mul1r.
- split.
  + by move=> f g hf hg; rewrite (monotone_daniell_integral_add hM hf hg) mulrDr.
  + by move=> d f hd hf; rewrite (monotone_daniell_integral_scale hM hd hf) mulrCA.
  + by move=> f g hf hg hfg; rewrite ler_pM2l // (monotone_daniell_integral_monotone hM hf hg hfg).
  + move=> f g hf hg hfg.
    have h := extended_positive_weight_increases hc (monotone_daniell_integral_increases hM hf hg hfg).
    have -> : (fun n => (c * lambda (f n))%:E) = (fun n => (c%:E * (lambda (f n))%:E)%E).
      by apply: funext=> n; rewrite EFinM.
    by rewrite EFinM.
- exists u=> //; apply/eqP; rewrite mulf_neq0 //; first by rewrite gt_eqF.
  exact/eqP.
Qed.

End HaarScaling.

Section NormalisedHaar.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hGc : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hc : compact [set: G].
Local Notation K := (@compactly_supported_continuous_functions R G).

(** Source for [is_normalised_haar_measure]: "a ... left and right
    Haar measure theta_n over O(n) such that theta_n[O(n)] = 1",
    Federer 2.7.16, p. 139, for a compact group G: a left Haar measure
    (2.7.2, p. 122) with total measure 1. Definition; the right Haar
    property follows (normalised_haar_measure_right). *)
Definition is_normalised_haar_measure (theta : set G -> \bar R) : Prop :=
  is_left_haar_measure mul theta /\ theta [set: G] = 1%E.

(** Source for [normalised_haar_measure_right]: a left Haar measure of
    the compact group G is a right Haar measure, "left and right Haar
    measure", Federer 2.7.16, p. 139, by 2.7.12, p. 129. Supporting
    lemma. *)
Lemma normalised_haar_measure_right (theta : set G -> \bar R) :
  is_normalised_haar_measure theta -> is_right_haar_measure mul inv theta.
Proof. by case=> h _; exact/(compact_group_haar_measures_coincide hGc hc). Qed.

(** Source for [left_haar_integral_total_positive]: a left Haar
    integral lambda of the compact group G satisfies lambda(1) > 0,
    supporting the normalisation of Federer 2.7.16, p. 139. Supporting
    lemma: lambda(1) = phi(G) for the associated measure phi
    (compact_representing_measure_total), and 0 < phi(G) (2.7.17,
    p. 141, compact_right_haar_measure_total). *)
Lemma left_haar_integral_total_positive (lambda : (G -> R) -> R) :
  is_left_haar_integral mul lambda -> 0 < lambda (fun _ => 1).
Proof.
move=> hl; have [phi [hphi hm hrep _ _]] := nonzero_invariant_measure_exists hl.
have [hpos _] := compact_right_haar_measure_total hGc hc
  ((compact_group_haar_measures_coincide hGc hc phi).1 hphi).
by rewrite (compact_representing_measure_total hc hm hrep) lte_fin in hpos.
Qed.

(** Source for [normalised_haar_measure_exists]: "there exists a ...
    left and right Haar measure theta_n over O(n) such that
    theta_n[O(n)] = 1", Federer 2.7.16, p. 139, for every compact group
    G. Existence: for a left Haar integral lambda (2.7.5, p. 125) the
    integral lambda(1)^{-1} lambda is a left Haar integral whose
    associated measure (2.5.3, p. 94) has total measure 1. *)
Theorem normalised_haar_measure_exists :
  exists theta : set G -> \bar R, is_normalised_haar_measure theta.
Proof.
have [lambda hl] := left_haar_integral_exists R hGc.
have hpos := left_haar_integral_total_positive hl.
have hinv : 0 < (lambda (fun _ => 1))^-1 by rewrite invr_gt0.
have hl' := nonzero_invariant_integral_scale hinv hl.
have [theta [htheta hm hrep _ _]] := nonzero_invariant_measure_exists hl'.
exists theta; split=> //.
by rewrite (compact_representing_measure_total hc hm hrep) mulVf ?gt_eqF.
Qed.

(** Source for [normalised_haar_measure_unique]: "there exists a
    unique left and right Haar measure theta_n over O(n) such that
    theta_n[O(n)] = 1", Federer 2.7.16, p. 139, the uniqueness, for
    every compact group G: two left or right Haar measures with total
    measure 1 coincide. Proof supplied: by 2.7.7, p. 125, the associated
    integrals differ by a positive factor c; the values at the constant
    function 1 give c = 1; the K(G) regular measure representing an
    integral is unique (2.5.3, p. 94). *)
Theorem normalised_haar_measure_unique (theta psi : set G -> \bar R) :
  is_left_haar_measure mul theta \/ is_right_haar_measure mul inv theta ->
  is_left_haar_measure mul psi \/ is_right_haar_measure mul inv psi ->
  theta [set: G] = 1%E -> psi [set: G] = 1%E -> theta = psi.
Proof.
have hleft phi : is_left_haar_measure mul phi \/ is_right_haar_measure mul inv phi ->
    is_left_haar_measure mul phi.
  by case=> // h; exact/(compact_group_haar_measures_coincide hGc hc).
move=> /hleft [l1 [hl1 hm1 hrep1 hreg1]] /hleft [l2 [hl2 hm2 hrep2 hreg2]] h1 h2.
have [c hc0 hlc] := left_haar_integral_unique hGc hl1 hl2.
have he1 := compact_representing_measure_total hc hm1 hrep1.
have he2 := compact_representing_measure_total hc hm2 hrep2.
have hone := compact_space_constant_one R hc.
have e1 : l1 (fun _ => 1) = 1 by move: h1; rewrite he1; case.
have e2 : l2 (fun _ => 1) = 1 by move: h2; rewrite he2; case.
have hc1 : c = 1 by move: e1; rewrite (hlc _ hone) e2 mulr1.
have hrep2' : is_real_integral_functional psi K l1.
  by move=> u hu; rewrite (hlc u hu) hc1 mul1r; exact: hrep2.
apply: funext=> S.
exact: (function_lattice_regular_representation_unique
  (@compactly_supported_continuous_functions_lattice R G) hm1 hm2 hrep1 hrep2' hreg1 hreg2 S).
Qed.

(** Source for [compact_group_unique_haar_measure]: "there exists a
    unique left and right Haar measure theta_n over O(n) such that
    theta_n[O(n)] = 1", Federer 2.7.16, p. 139, for every compact group
    G satisfying the standing hypothesis of 2.7.1, p. 121. Direct
    formalisation: theta is a left and a right Haar measure with
    theta(G) = 1, and every left or right Haar measure psi with
    psi(G) = 1 equals theta. *)
Theorem compact_group_unique_haar_measure :
  exists theta : set G -> \bar R,
    [/\ is_left_haar_measure mul theta, is_right_haar_measure mul inv theta,
      theta [set: G] = 1%E &
      forall psi, is_left_haar_measure mul psi \/ is_right_haar_measure mul inv psi ->
        psi [set: G] = 1%E -> psi = theta].
Proof.
have [theta [hl h1]] := normalised_haar_measure_exists.
exists theta; split=> //.
- exact: normalised_haar_measure_right.
- move=> psi hpsi hpsi1; apply: (normalised_haar_measure_unique hpsi _ hpsi1 h1).
  by left.
Qed.

End NormalisedHaar.

Arguments is_normalised_haar_measure {R G} mul theta.
