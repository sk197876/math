(** Federer (1969), 3.2.7, p. 246:
    existence of the auxiliary signed square root.
    This witness is private to its sealing module and
    the assumptions audit. Downstream proofs use its
    defining half-line laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SignedSquareRootUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [signed_square_root_exists]: supporting
    scalar existence for the third example of Federer
    3.2.7, p. 246. Positive and negative
    scalar parts give an explicit witness of the
    independently specified laws, with no added axiom. *)
Theorem signed_square_root_exists (R:realType):exists G:R->R,is_signed_square_root G.
Proof.
exists (fun x=>Num.sqrt (Num.max x 0)-Num.sqrt (Num.max (-x) 0)); constructor=>x hx.
- have hn: -x<= 0 by rewrite oppr_le0.
  by rewrite (max_l hx) (max_r hn) sqrtr0 subr0.
- have hn:0<= -x by rewrite oppr_ge0.
  by rewrite (max_r hx) (max_l hn) sqrtr0 sub0r.
Qed.
