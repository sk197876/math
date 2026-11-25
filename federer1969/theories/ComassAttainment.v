(** Federer (1969), 1.8.1, p. 38: attainment of the comass supremum, used
    for its equality case. This property is proved after the supremum
    specification and is not built into its definition. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology
  InnerExterior InnerExteriorPositivity InnerExteriorIsomorphism
  InnerCoordinateContinuity OrthonormalFamilies
  SimpleUnitBall SimpleUnitCompact ComassUP CompactMaximum
  ExteriorGrading AlternatingCoordinates AlternatingPairing LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Attainment.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Local Notation E := (inner_metric_space (@exterior_inner_productP R h2 V B hB m)).

(** Source for [exterior_pairing_continuous]: Federer 1.8.1,
    p. 38, supporting continuity for maximising evaluations on S.
    In finite dimension gamma represents every covector, reducing
    this to continuity of an inner-product coordinate. *)
Theorem exterior_pairing_continuous (phi : A_m V R^o m) :
  continuous (fun x : E => (pairing x phi : R^o)).
Proof.
have [g [hfg hgf]] := @inner_exterior_inverse_exists R h2 V B hB n e he m.
have hf : (fun x : E => (pairing x phi : R^o)) =
    inner_coordinate (@exterior_inner_productP R h2 V B hB m) (g phi).
  apply: funext => x; by rewrite inner_coordinateE /exterior_inner_form hgf.
rewrite hf; exact: inner_coordinate_continuous.
Qed.

(** Source for [comass_attained]: Federer 1.8.1, p. 38, supporting
    attainment of the first supremum This includes zero covectors and
    positive degrees above the ambient dimension. *)
Theorem comass_attained (phi : A_m V R^o m) c :
  (0 < m)%N -> is_comass h2 hB phi c ->
  exists x, simple_unit_ball h2 hB x /\ pairing x phi = c.
Proof.
move=> hm hc.
have hn : (@simple_unit_ball R h2 V B hB m) !=set0.
  exists 0; exact: simple_unit_ball_zero.
have hcompact := @simple_unit_ball_compact R h2 V B hB n e he m hm.
have [x [hx hmax]] := @continuous_compact_maximum R (Topological.clone E _)
  (@simple_unit_ball R h2 V B hB m) (fun x => pairing x phi)
  hn hcompact (@exterior_pairing_continuous phi).
exists x; split=> //; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@comass_upper_law R h2 V B hB m phi c hc x hx).
- exact (@comass_least_upper_bound R h2 V B hB m phi c hc (pairing x phi) hmax).
Qed.
End Attainment.
