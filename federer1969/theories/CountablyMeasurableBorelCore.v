(** Federer (1969), 3.2.5, p. 245: a measurable
    subset of a countably measurable image is a Borel set
    together with a null set. Supporting extension of the
    finite Borel sandwich in 2.2.3, p. 61, using 2.3.4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureAlmostBasic BorelRegularMeasureUP BorelRegularSandwich
  TopologicalBorel CountablyMeasurableUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_measurable_borel_core]: the Borel
    plus null decomposition used in Federer 3.2.5, p. 245.
    Only the set A, rather than the whole ambient measure,
    is required to be countably measurable. *)
Theorem countably_measurable_borel_core (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_borel_regular_measure mu) A:
  measure_countably_measurable mu A ->
  exists D,borel_set D /\ D `<=` A /\ mu (A `\` D)=0.
Proof.
move=>[F [hF [hUnion hFinite]]].
have hex B:exists D:set X,F B -> borel_set D /\ D `<=` B /\ mu (B `\` D)=0.
  case:(pselect (F B))=>hB.
  - have [D [E [hD [hE [hDB [hBE hNull]]]]]]:=
      borel_regular_finite_sandwich hm hr (hFinite B hB).1 (hFinite B hB).2.
    exists D=>_; split=>//; split=>//.
    apply:(measure_null_subset hm _ hNull).
    by move=>x [hx hn]; split=>//; exact (hBE x hx).
  - exists set0=>h; exfalso; exact (hB h).
have [D hD]:=choice hex.
pose C:=\bigcup_(B in F) D B.
have hCB:borel_set C.
  apply:borel_set_countable_union; first exact hF.
  move=>B hB; exact (hD B hB).1.
have hCA:C `<=` A.
  move=>x [B hB hx]; rewrite hUnion; exists B=>//; exact ((hD B hB).2.1 x hx).
have hExcess:A `\` C `<=` \bigcup_(B in F) (B `\` D B).
  move=>x [hx hNot]; rewrite hUnion in hx; have [B hB hxB]:=hx.
  exists B=>//; split=>//; move=>hDx; apply:hNot; by exists B.
exists C; split=>//; split=>//.
apply:(measure_null_subset hm hExcess).
apply:(measure_null_countable_union hm hF)=>B hB; exact (hD B hB).2.2.
Qed.
