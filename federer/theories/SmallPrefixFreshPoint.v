(** Cardinal step supporting Federer (1969), 2.2.4, p. 62 At a stage whose
    predecessors have cardinality strictly less than D, their selected image
    cannot exhaust a set containing a copy of D. We express the predecessor
    functions dependently so no arbitrary value outside their domains is
    needed. Source context: SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality wochoice.
From Federer Require Import CardinalSuccessorUP CardinalInjection
  SmallPrefixWellOrderUP WellOrderRecursionBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [small_prefix_fresh_point]: supporting fresh-point argument
    in Federer 2.2.4, p. 62. An image of the proper predecessor set has no
    greater cardinality than that set, hence cannot cover a prescribed set
    of full cardinality. *)
Lemma small_prefix_fresh_point (J T : choiceType) (D C : set J) (r : rel J)
    (a : set_type C) (B : set T) :
  is_small_prefix_well_order D C r -> D #<= B ->
  forall f : forall b : set_type C, strict_well_order_relation r (val b) (val a) -> T,
  exists x, B x /\ forall b h, x <> f b h.
Proof.
move=> hw hB f.
pose P := [set b : set_type C | strict_well_order_relation r (val b) (val a)].
pose F (p : set_type P) := f (val p) (set_valP p).
pose S := F @` setT.
have hp : (@setT (set_type P)) #<= well_order_prefix C r (val a).
  apply: (@cardinal_bound_of_injection _ _ setT (well_order_prefix C r (val a))
    (fun p : set_type P => (val (val p) : J))).
  - move=> p _; split; first exact: set_valP.
    exact: set_valP p.
  - move=> p q _ _ he; apply: val_inj; exact: val_inj he.
have hs : S #<= well_order_prefix C r (val a).
  exact: card_le_trans (card_image_le F setT) hp.
have hex : exists x, B x /\ ~ S x.
  apply: contrapT=> hn.
  have hsub : B `<=` S by move=> x hx; apply: contrapT=> hnS; apply: hn; exists x; split.
  have hh := card_le_trans hB (card_le_trans (subset_card_le hsub) hs).
  exact: (@small_prefix_strict_cardinal J D C r hw (val a) (set_valP a) hh).
have [x [hx hn]] := hex; exists x; split=> // b h he.
pose p : set_type P := @exist (set_type C) (fun z => z \in P) b (mem_set h).
have hF : F p = f b h.
  rewrite /F /=; congr (f b _); exact: Prop_irrelevance.
apply: hn; exists p; first exact Logic.I.
by rewrite hF -he.
Qed.
