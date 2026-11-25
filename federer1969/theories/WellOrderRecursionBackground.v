(** Set-theoretic recursion background for Federer (1969), 2.2.4, p. 62. We
    derive well-foundedness of the strict relation from the least-element
    property. The narrow Corelib.Init.Wf import supplies the logical
    accessibility predicate and its inductive eliminator, not a
    set-selection theorem. Source context:
    SeparableMetricBaseConstruction.v. *)
From Corelib Require Import Init.Wf.
From mathcomp Require Import all_boot boolp classical_sets wochoice.
From Federer Require Import WellOrderLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [strict_well_order_relation]: supporting strict predecessor
    relation for the recursion in Federer 2.2.4, p. 62 The ambient MathComp
    well ordering is reflexive, hence x<>y is explicit. *)
Definition strict_well_order_relation (J : eqType) (r : rel J) (x y : J) : Prop :=
  r x y /\ x <> y.

(** Source for [strict_well_order_well_founded]: supporting accessibility
    theorem for the recursion in Federer 2.2.4, p. 62 If a nonaccessible
    point existed, its least such point would have only accessible
    predecessors, a contradiction. *)
Lemma strict_well_order_well_founded (J : eqType) (r : rel J) :
  well_order r -> well_founded (strict_well_order_relation r).
Proof.
move=> hw x; apply: contrapT=> hx.
have hn : exists z, ~ Acc (strict_well_order_relation r) z by exists x.
have [z [hz hmin]] := well_order_set_minimum hw hn.
apply: hz; constructor=> y [hy hne]; apply: contrapT=> hbad.
have hzy := hmin y hbad; apply: hne.
apply: (well_order_antisymmetric_law hw); by apply/andP; split.
Qed.

(** Source for [well_founded_pullback]: supporting restriction of the
    recursion order to an actual carrier subtype in Federer 2.2.4, p. 62
    Pulling back a well-founded relation preserves accessibility. *)
Lemma well_founded_pullback (I J : Type) (r : J -> J -> Prop) (f : I -> J) :
  well_founded r -> well_founded (fun x y => r (f x) (f y)).
Proof.
move=> hw x; have ha := hw (f x).
suff h : forall z, Acc r z -> forall y, f y = z -> Acc (fun a b => r (f a) (f b)) y.
  exact: h (f x) ha x (erefl _).
move=> z hz; elim: z / hz=> z hz ih y hy; constructor=> u hu.
apply: (ih (f u)); first by rewrite -hy.
by [].
Qed.
