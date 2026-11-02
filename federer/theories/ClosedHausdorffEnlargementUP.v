(** Federer (1969), 2.10.24, p. 188, Hausdorff application of the
    enlargement criterion on p. 187. Use closed generators from 2.10.2(1),
    p. 171, and the closure of the diameter enlargement of 2.10.18, p. 180.
    One positive finite constant controls diameter and cost, including zero
    costs. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [closed_hausdorff_enlargement_control]: supporting
    auxiliary constant for the Hausdorff application in
    2.10.24, p. 188. Five controls diameter and
    5^m controls the integer Hausdorff gauge; their sum
    is an allowed common control, without affecting
    the equality criterion. *)
Definition closed_hausdorff_enlargement_control (R : realType) (m : nat) := (5+(5:R)^+m)%R.

(** Source for [closed_hausdorff_enlargement_control_bounds]:
    supporting positivity and the two scalar bounds
    for the application in 2.10.24, p. 188. *)
Lemma closed_hausdorff_enlargement_control_bounds (R : realType) (m : nat) :
  0<closed_hausdorff_enlargement_control R m /\
  5<=closed_hausdorff_enlargement_control R m /\
  (5:R)^+m<=closed_hausdorff_enlargement_control R m.
Proof.
have hp : 0<(5:R)^+m by rewrite exprn_gt0 // ltr0n.
rewrite /closed_hausdorff_enlargement_control; split; [lra|split; lra].
Qed.
