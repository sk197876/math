(** Federer (1969), Theorem 2.8.2, pp. 142–143. The contraction function is
    defined on the target family itself. This interface
    derives the result from the abstract finite-open-cover and exhaustion
    laws. The erratum's correction of the preliminary empty selection (p. 3,
    book p. 142 line 33) is recorded in ContractionCoverUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import CoveringFamilyUP ContractionCoverUP
  FiniteOpenMeasureCover CountableTargetContractionCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_2_8_2]: direct formalisation of the theorem in
    Federer 2.8.2, p. 142. Every target A in K has its own factor strictly
    between zero and one; in every open W a countable disjointed subfamily
    of F lies in W and leaves at most sigma(A) times mu(W intersect A)
    uncovered. Then F is adequate for union K. Targets need not be bounded
    or measurable; boundedness is only an intermediate proof reduction. *)
Theorem federer_2_8_2 (R : realType) (X : metricType R)
    (F K : set (set X)) (mu : set X -> \bar R)
    (sigma : {A : set X | K A} -> R) :
  is_covering_theory_context F mu -> countable K ->
  (forall A, (0 < sigma A < 1)%R) ->
  (forall A, has_local_cover_contraction mu F (sval A) (sigma A)) ->
  family_is_measure_adequate mu F (\bigcup_(A in K) A).
Proof.
move=> hc hK hsigma hlocal.
pose s A := match pselect (K A) with
  | left h => sigma (exist K A h)
  | right _ => 0%R
  end.
have hs A (hA : K A) : (0 < s A < 1)%R.
  rewrite /s; case: (pselect (K A))=> [h|h]; last by contradiction.
  exact: hsigma.
have hl A (hA : K A) : has_local_cover_contraction mu F A (s A).
  rewrite /s; case: (pselect (K A))=> [h|h]; last by contradiction.
  exact: (hlocal (exist K A h)).
have [U hU] := covering_context_finite_open_cover hc.
exact (@countable_target_contraction_adequacy R X mu (covering_context_measure hc)
  F K s U (covering_context_closed hc) (covering_context_open_measurable hc)
  hU hK hs hl).
Qed.
