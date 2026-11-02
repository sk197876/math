(** Private selection construction for Federer (1969), 2.2.4, p. 62 We
    wellorder the two requests per family member together, using the proved
    binary-prefix cardinal bound. A full-cardinality small-prefix
    representative supplies all stages; stages without requests use a fixed
    family member. One fresh point is chosen at each stage. The two
    resulting selections have disjoint ranges, just as in Federer's paired
    recursion. This documented interleaving avoids a separate general
    infinite-cardinal multiplication theorem. Source context:
    SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals wochoice.
From Federer Require Import SequenceSpace SequenceCoordinates CardinalInjection WellOrderLaws
  SmallPrefixWellOrderUP SmallPrefixWellOrderSealed WellOrderRecursionBackground
  SmallPrefixFreshPoint FreshTransfiniteSelectionConstruction SequenceDoubleCardinality
  DisjointSelectionsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [full_cardinality_disjoint_selections_exist]: existence of
    the disjoint selections in Federer 2.2.4, p. 62. The cardinality
    premises will be proved from Federer's measure and topology hypotheses
    in the public theorem. *)
Theorem full_cardinality_disjoint_selections_exist (R : realType)
    (I T : choiceType) (E : I -> set T) (i0 : I) :
  (@setT I) #<= (@setT (positive_sequence_space R)) ->
  (forall i, (@setT (positive_sequence_space R)) #<= E i) ->
  exists f g, is_disjoint_family_selection E f g.
Proof.
move=> hI hE.
pose N := positive_sequence_space R.
pose W := @SmallPrefixWellOrder.value [the choiceType of N] setT.
pose C := W.1; pose r := W.2.
have hW : is_small_prefix_well_order setT C r := @SmallPrefixWellOrder.laws [the choiceType of N] setT.
have hw := small_prefix_well_order_law hW.
have hcode : (@setT (I * bool)) #<= C.
  exact: card_le_trans (sequence_cardinal_bound_doubled hI) (small_prefix_representative_cardinal hW).
have [code [hc hinj]] := cardinal_injection_with_default (positive_sequence_default R) hcode.
have hcodeC p : C (code p) := hc p Logic.I.
pose stage p : set_type C := @exist N (fun n => n \in C) (code p) (mem_set (hcodeC p)).
have hstage : injective stage.
  move=> p q he; have hh := congr1 (fun a : set_type C => (val a : N)) he.
  apply: hinj hh; by rewrite inE.
have hrequest a : exists p : I * bool, forall q, stage q = a -> p = q.
  case: (pselect (exists q, stage q = a))=> [[q hq]|hn].
  - exists q=> p hp; apply: hstage; by rewrite hq hp.
  - exists (i0,false)=> q hq; exfalso; apply: hn; by exists q.
pose request a := projT1 (cid (hrequest a)).
have hr a q : stage q = a -> request a = q := projT2 (cid (hrequest a)) q.
pose relstage (a b : set_type C) := strict_well_order_relation r (val a) (val b).
have hwell : well_founded relstage.
  exact: (@well_founded_pullback (set_type C) N (strict_well_order_relation r)
    (fun a : set_type C => (val a : N)) (strict_well_order_well_founded hw)).
pose F a := E (request a).1.
have hfresh a (f : forall b, relstage b a -> T) :
    exists x, F a x /\ forall b h, x <> f b h.
  exact: (@small_prefix_fresh_point [the choiceType of N] T setT C r a (F a) hW (hE _) f).
have [s hs] := @well_founded_fresh_selection_exists (set_type C) T relstage F hwell hfresh.
have hsinj : injective s.
  move=> a b he; case: (eqVneq a b)=> [hab|hab]; first exact hab.
  have hne : (val a : N) <> val b.
    move=> hv; have hab' : a = b by apply: val_inj; exact hv.
    by rewrite hab' eqxx in hab.
  have /orP[habr|hbar] := well_order_total_law hw (val a) (val b).
  - exfalso; apply: ((hs b).2 a); first by split.
    exact: esym he.
  - exfalso; apply: ((hs a).2 b); first by split=> // h; apply: hne; exact: esym h.
    exact he.
exists (fun i => s (stage (i,true))), (fun i => s (stage (i,false))).
constructor.
- move=> i; have hh := (hs (stage (i,true))).1.
  by rewrite /F (hr _ _ (erefl _)) in hh.
- move=> i; have hh := (hs (stage (i,false))).1.
  by rewrite /F (hr _ _ (erefl _)) in hh.
- move=> i j he; have hp := hstage _ _ (hsinj _ _ he).
  by have := congr1 (fun p : I * bool => p.2) hp.
Qed.
