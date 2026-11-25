(** Private transfinite construction supporting Federer (1969), 2.5.11, p.
    102: "For j in {1,2} let Y_j be a set with cardinal number aleph_j". If
    D is well ordered so that every proper initial segment of D has cardinal
    at most that of A, and B does not have cardinal at most that of A, then
    D has cardinal at most that of B: a fresh transfinite selection maps
    each member of D to a member of B distinct from the values at its
    predecessors, since the image of an initial segment cannot cover B. This
    is the comparison used to show that the least initial segment of a well
    ordering which is too large is a successor cardinal (Kelley, General
    Topology, Appendix, Theorems 150 and 157, p. 275, Dover 2017 reprint of
    1955). *)
From mathcomp Require Import all_boot boolp classical_sets cardinality wochoice.
From Federer Require Import CardinalSuccessorUP CardinalInjection WellOrderLaws
  WellOrderRecursionBackground FreshTransfiniteSelectionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [small_prefix_fresh_value]: supporting fresh-point
    step for the sets Y_j of Federer 2.5.11, p. 102. The values at
    the predecessors of a form an image of a proper initial segment,
    whose cardinal is at most that of A; hence they do not cover B. *)
Lemma small_prefix_fresh_value (I J K : choiceType) (A : set I) (D : set J) (r : rel J)
    (B : set K) (a : set_type D) :
  (forall x, D x -> well_order_prefix D r x #<= A) -> ~ (B #<= A) ->
  forall f : forall b : set_type D, strict_well_order_relation r (val b) (val a) -> K,
  exists x, B x /\ forall b h, x <> f b h.
Proof.
move=> hp hB f.
pose P := [set b : set_type D | strict_well_order_relation r (val b) (val a)].
pose F (p : set_type P) := f (val p) (set_valP p).
pose S := F @` setT.
have hpre : (@setT (set_type P)) #<= well_order_prefix D r (val a).
  apply: (@cardinal_bound_of_injection _ _ setT (well_order_prefix D r (val a))
    (fun p : set_type P => (val (val p) : J))).
  - move=> p _; split; first exact: set_valP.
    exact: set_valP p.
  - move=> p q _ _ he; apply: val_inj; exact: val_inj he.
have hs : S #<= A.
  apply: card_le_trans (card_image_le F setT) _.
  exact: card_le_trans hpre (hp _ (set_valP a)).
have hex : exists x, B x /\ ~ S x.
  apply: contrapT=> hn.
  have hsub : B `<=` S by move=> x hx; apply: contrapT=> hnS; apply: hn; exists x; split.
  exact: hB (card_le_trans (subset_card_le hsub) hs).
have [x [hx hn]] := hex; exists x; split=> // b h he.
pose p : set_type P := @exist (set_type D) (fun z => z \in P) b (mem_set h).
have hF : F p = f b h.
  rewrite /F /=; congr (f b _); exact: Prop_irrelevance.
apply: hn; exists p; first exact Logic.I.
by rewrite hF -he.
Qed.

(** Source for [small_prefix_injects_exists]: supporting
    comparison for the sets Y_j of Federer 2.5.11, p. 102; Kelley,
    Appendix, Theorems 150 and 157, p. 275. Well-founded recursion
    along D selects pairwise distinct members of B. *)
Theorem small_prefix_injects_exists (I J K : choiceType) (A : set I) (D : set J) (r : rel J)
    (B : set K) :
  well_order r -> (forall x, D x -> well_order_prefix D r x #<= A) -> ~ (B #<= A) -> D #<= B.
Proof.
move=> hw hp hB.
pose s (a b : set_type D) := strict_well_order_relation r (val a) (val b).
have hwf : well_founded s.
  exact: (@well_founded_pullback (set_type D) J (strict_well_order_relation r) val
    (strict_well_order_well_founded hw)).
have [f hf] := @well_founded_fresh_selection_exists (set_type D) K s (fun _ => B) hwf
  (fun a g => @small_prefix_fresh_value I J K A D r B a hp hB g).
have hinj : forall a b : set_type D, f a = f b -> a = b.
  move=> a b he; apply: contrapT=> hne.
  have hv : val a <> val b by move=> h; apply: hne; exact: val_inj h.
  case/orP: (well_order_total_law hw (val a) (val b))=> hab.
  - exact: (hf b).2 a (conj hab hv) (esym he).
  - exact: (hf a).2 b (conj hab (fun h => hv (esym h))) he.
have hT : (@setT (set_type D)) #<= B.
  apply: (@cardinal_bound_of_injection _ _ setT B f).
  - move=> a _; exact: (hf a).1.
  - move=> a b _ _; exact: hinj.
have := card_setT_sym D; move/card_eqPle=> [hD _].
exact: card_le_trans hD hT.
Qed.
