(** General topology for the restriction f|C in Federer (1969), 2.3.5, pp.
    76–77. Relative open inverse images express continuity without choosing
    values outside C or assuming that the target is inhabited. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function_continuous_on]: abstract continuity
    of f|C in Federer 2.3.5, p. 77. Each open inverse image
    on C is C intersected with an ambient open set. *)
Record partial_function_continuous_on (X Y : topologicalType)
    (C : set X) (f : partial_function X Y) : Prop := {
  (** Source for [partial_continuity_domain]: Supporting Federer 2.3.5. *)
  partial_continuity_domain : C `<=` partial_function_domain f;
  (** Source for [partial_continuity_open]: relative inverse-image
      definition of continuity in Federer 2.3.5, p. 77. *)
  partial_continuity_open : forall U, open U -> exists V, open V /\
    C `&` partial_function_preimage f U = C `&` V
}.

(** Source for [partial_continuity_subset]: supporting restriction
    to the common closed set C in Federer 2.3.5, p. 77. *)
Lemma partial_continuity_subset (X Y : topologicalType) (C E : set X)
    (f : partial_function X Y) : C `<=` E ->
  partial_function_continuous_on E f -> partial_function_continuous_on C f.
Proof.
move=> hs hf; constructor.
- move=> x hx; exact (@partial_continuity_domain X Y E f hf x (hs x hx)).
- move=> U hU; have [V [hV he]] := partial_continuity_open hf hU.
  exists V; split=> //; apply/seteqP; split=> x [hx hy]; split=> //.
  + have hh : (E `&` partial_function_preimage f U) x by split=> //; exact: hs x hx.
    by rewrite he in hh; exact: hh.2.
  + have hh : (E `&` V) x by split=> //; exact: hs x hx.
    by rewrite -he in hh; exact: hh.2.
Qed.
