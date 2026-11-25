(** Federer (1969), 2.10.22, pp. 184–185: supporting finite maximum for
    ordering the costs of a near-optimal countable cover. This is elementary
    finite set/order background for the compact-cover argument, not a
    separate printed theorem. Source context and proof context:
    CompactGeneratorCostUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_nonempty_real_maximum]: supporting
    finite order fact for the cover selection in
    2.10.22, pp. 184–185. No topology or
    arbitrary supremum is required on a finite nonempty set. *)
Lemma finite_nonempty_real_maximum (R : realType) (I : choiceType)
    (A : set I) (w : I -> R) : finite_set A -> A !=set0 ->
  exists a, A a /\ forall x, A x -> w x<=w a.
Proof.
move=> /finite_fsetP [F ->].
elim/fset1U_rect: F=> [|a F ha ih] hne.
- have [x hx] := hne; by rewrite /= inE in hx.
- case: (pselect ([set` F] !=set0))=> [hF|hF].
  + have [b [hb hmax]] := ih hF.
    case: (leP (w a) (w b))=> hab.
    * exists b; split; first exact: fset1Ur hb.
      move=> x hx; have hmem : x \in (a |` F)%fset := hx.
      move/fset1UP: hmem=> [->|hxF]; first exact hab; exact: hmax x hxF.
    * exists a; split; first exact: fset1U1.
      move=> x hx; have hmem : x \in (a |` F)%fset := hx.
      move/fset1UP: hmem=> [->|hxF]; first exact: lexx.
      exact: le_trans (hmax x hxF) (ltW hab).
  + exists a; split; first exact: fset1U1.
    move=> x hx; have hmem : x \in (a |` F)%fset := hx.
    move/fset1UP: hmem=> [->|hxF]; first exact: lexx.
    exfalso; apply: hF; by exists x.
Qed.
