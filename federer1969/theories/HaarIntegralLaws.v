(** Federer (1969), 2.7.2, printed p. 122: "a nonzero monotone left
    invariant integral (measure) is called a left Haar integral (measure) of
    G", and similarly on the right. HaarIntegralUP.v reads a nonzero
    monotone invariant measure as the K(X) regular measure associated with a
    nonzero monotone invariant integral. This file shows that the reading
    agrees with the words: such a measure is an invariant measure in the
    sense of 2.7.1, p. 122, and it is not the zero measure, since the
    integral of every u in K(X) with respect to the zero measure is 0
    (2.4.2-2.4.4). Moreover every nonzero monotone invariant integral has
    exactly one associated K(X) regular measure (2.5.2-2.5.3, pp. 92-95).
    The statements are made for an arbitrary action A and apply to left and
    right Haar integrals and measures by unfolding the definitions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import FunctionLatticeUP MonotoneDaniellIntegralUP CompactSupportFunctionUP
  CompactSupportFunctionLattice FunctionLatticeRegularityUP RealIntegralFunctionalUP MeasureUP
  SummableRealFunctionUP MeasureIntegralUP MeasureIntegralUniqueness MeasureConullZeroIntegral
  DaniellEmptyBoundary
  RegularDaniellRepresentation CovariantIntegralUP HaarIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section NonzeroInvariantMeasures.
Variable R : realType.
Variable G : Type.
Variable X : topologicalType.
Variable A : G -> X -> X.
Local Notation K := (@compactly_supported_continuous_functions R X).

(** Source for [nonzero_invariant_measure_invariant]: a left (right)
    Haar measure of Federer 2.7.2, p. 122, is a left (right) invariant
    measure in the sense of 2.7.1, p. 122. Supporting lemma for an
    arbitrary action. *)
Lemma nonzero_invariant_measure_invariant (phi : set X -> \bar R) :
  is_nonzero_monotone_invariant_measure A phi -> is_invariant_measure A phi.
Proof.
case=> mu [[[_ hc] hm _] hphi hi hr].
by exists mu; split.
Qed.

(** Source for [nonzero_invariant_measure_nonzero]: "nonzero" in
    "a nonzero monotone left invariant ... (measure)", Federer 2.7.2,
    p. 122: a left (right) Haar measure is not the zero measure. If phi
    vanished identically, the integral of u with respect to phi would be
    0 for every u in K(X), by the uniqueness of integrals (2.4.4), and
    the associated integral would vanish on K(X). *)
Theorem nonzero_invariant_measure_nonzero (phi : set X -> \bar R) :
  is_nonzero_monotone_invariant_measure A phi -> exists S, phi S <> 0%E.
Proof.
case=> mu [[_ _ [u hu hmu]] hphi hi _].
apply/not_existsP=> /(_ _) h0.
have hz : phi = fun _ => 0%E by apply: funext=> S; apply: contrapT; exact: h0.
have hiu := hi u hu; rewrite hz in hiu.
have hzi : is_measure_integral (fun _ : set X => (0 : \bar R)) (real_total_integrand u) 0%E.
  exact: (@measure_almost_zero_integral R X _ (@daniell_zero_measure R X)).
by apply: hmu; apply: EFin_inj; exact: measure_integral_unique hiu hzi.
Qed.

(** Source for [nonzero_invariant_measure_exists]: the K(X) regular
    measure associated with a left (right) Haar integral, which is by
    Federer 2.7.2, p. 122, a left (right) Haar measure, exists and is
    unique, by 2.5.2-2.5.3, pp. 92-95, as in 2.7.1, p. 122. *)
Theorem nonzero_invariant_measure_exists (mu : (X -> R) -> R) :
  is_nonzero_monotone_invariant_integral A mu ->
  exists phi : set X -> \bar R,
    [/\ is_nonzero_monotone_invariant_measure A phi, is_measure phi,
      is_real_integral_functional phi K mu, is_function_lattice_regular K phi &
      forall nu, is_measure nu -> is_real_integral_functional nu K mu ->
        is_function_lattice_regular K nu -> forall S, phi S = nu S].
Proof.
move=> hmu.
have hL := @compactly_supported_continuous_functions_lattice R X.
have hne : exists f, K f by exists (fun _ => 0); exact: compactly_supported_zero_function.
have [phi [hphi [hi [hr hu]]]] :=
  monotone_daniell_regular_representation hL (nonzero_invariant_integral_monotone hmu) hne.
by exists phi; split=> //; exists mu.
Qed.

End NonzeroInvariantMeasures.
