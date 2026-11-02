(** Federer (1969), 3.2.22(2), p. 258: a
    countably rectifiable fibre cover may omit a null
    remainder. This expands the definition 3.2.14(3),
    p. 251, rather than assuming a complete cover. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RectifiableSetUP MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_measure_rectifiable_null_remainder]:
    supporting assembly of coordinate fibres and the
    omitted null fibre in Federer 3.2.22(2), p. 258.
    Compose the two null remainders to obtain the
    countable (phi,m) rectifiability of the whole fibre. *)
Lemma countably_measure_rectifiable_null_remainder (R:realType) (X:metricType R)
    (phi:set X->\bar R) m (E C:set X):
  is_countably_measure_m_rectifiable phi m C ->phi (E `\` C)=0 ->
  is_countably_measure_m_rectifiable phi m E.
Proof.
move=>[hm [S [hS hNull]]] hEC; split; first exact hm.
exists S; split; first exact hS.
have hUnion:=measure_null_union hm hEC hNull.
apply:(measure_null_subset hm _ hUnion)=>x [hx hNotS].
have [hCx|hCx]:=pselect (C x).
- right; by split.
- left; by split.
Qed.
