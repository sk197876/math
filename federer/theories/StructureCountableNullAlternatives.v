(** Federer (1969), 3.3.4, p. 291: the
    null-exception conclusion after countable assembly of
    P_v, Q_v and R_v. No measurability of a
    hull difference is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic
  StructureCountableAlternatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_countable_alternatives_null]:
    H^m(T(U) minus (P union Q union R))=0,
    Federer 3.3.4, p. 291, follows from the
    per-v null exceptions and the actual decreasing
    Q_v and R_v. The original measurable target
    may be any set for this outer-measure step. *)
Theorem structure_countable_alternatives_null (R:realType) (X:choiceType)
    (mu:set X->\bar R) (T:set X) (P Q S:nat->set X):
  is_measure mu ->
  (forall i j,(i<=j)%N ->Q j `<=` Q i) ->
  (forall i j,(i<=j)%N ->S j `<=` S i) ->
  (forall i,mu (T `\` (P i `|` Q i `|` S i))=0) ->
  mu (T `\` ((\bigcup_i P i) `|` (\bigcap_i Q i) `|` (\bigcap_i S i)))=0.
Proof.
move=>hMu hQ hS hNull.
have hUnion:mu (\bigcup_i (T `\` (P i `|` Q i `|` S i)))=0.
  apply:(@measure_null_countable_union R X nat mu hMu setT
    (fun i=>T `\` (P i `|` Q i `|` S i)) (countableP setT)).
  by move=>i _; exact:hNull i.
apply:(@measure_null_subset R X mu hMu _ _ _ hUnion).
move=>x [hT hNot]; apply:contrapT=>hNo; apply:hNot.
apply:(structure_countable_alternatives_inclusion hQ hS).
move=>i _; apply:contrapT=>hBad; apply:hNo; exists i=>//; by split.
Qed.
