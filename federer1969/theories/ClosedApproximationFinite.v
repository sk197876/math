(** Federer (1969), 2.2.2, p. 61: minimality of the generated Borel family
    puts all Borel sets in the approximation class for the finite restricted
    measure. The intermediate theorem retains the general
    countable-closed-cover hypothesis, with metric spaces supplied by the
    local 2.2.1 development. Source context: ClosedApproximationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP CountablyClosedFamilyUP GeneratedClosed
  TopologicalBorel TopologicalBorelGeneration ClosedApproximationUP ClosedApproximationFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_borel_closed_approximable]: Federer
    2.2.2, p. 61, apply the 2.2.1 closed-generator criterion
    to the approximation class. This is the finite-total-measure
    step of the printed proof, before returning to the original measure. *)
Theorem finite_measure_borel_closed_approximable (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) :
  has_closed_sequence_covers T -> mu setT < +oo ->
  (forall K, closed K -> measure_measurable mu K) ->
  forall B, borel_set B -> is_closed_approximable mu B.
Proof.
move=> hcover hf hc.
have hclosed : forall A : set T, closed A -> A `<=` setT by move=> A _ x _.
pose F := generated_closed_family false hclosed.
have hF : is_generated_closed_family false setT (@closed T) F.
  exact: generated_closed_family_specification.
have he : F = @borel_set T := borel_generated_by_closed_closure hcover hF.
have hin : F `<=` is_closed_approximable mu.
  apply: (@generated_closed_family_least false _ setT (@closed T) F hF).
  - exact: closed_approximable_countably_closed hm hf hc.
  - move=> A hA; exact: (@closed_set_approximable R T mu hm A hA).
by rewrite -he.
Qed.
