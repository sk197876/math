(** Federer (1969), 2.5.15, p. 108: point evaluation is integration against
    a unit point mass. This supporting total-real formula supplies the
    atomic regressions for the endpoint conventions of 2.6.7, p. 121. It
    follows from the constant integral and invariance under null changes,
    2.4.4(1), p. 82, and 2.4.3(2), p. 81. it does not state this identical
    regression lemma. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionBasic MeasureAlmostUP
  MeasureIntegralUP MeasureIntegralAlmostEquality SummableRealFunctionUP
  PointMassMeasure ProbabilityConstantIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [point_mass_real_integral]: total real
    point-evaluation formula from Federer 2.5.15, p. 108,
    used to check atoms in 2.6.7, p. 121. Every function
    is measurable for a point mass, since its restriction to
    the one-point conull set agrees with a constant. *)
Lemma point_mass_real_integral (R : realType) (X : choiceType)
    (c : X) (f : X -> R) :
  is_measure_integral (point_mass R c) (real_total_integrand f) (f c)%:E.
Proof.
have hm := @point_mass_is_measure R X c.
have hprob : point_mass R c setT = 1%E := point_mass_in R (I : setT c).
have hi := @probability_constant_integral R X (point_mass R c) hm (f c) hprob.
apply: (@measure_integral_almost_equal R X (point_mass R c) hm _ _ (f c)%:E hi).
apply: (@point_mass_out R X c _)=> hn; apply: hn.
exists (f c)%:E; split=> //; by apply/real_total_integrand_graph.
Qed.
