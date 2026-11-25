(** Federer (1969), proof of 2.5.2, p. 93: the equally spaced nonnegative
    truncation levels n epsilon. These elementary scalar identities support
    the finite layer induction, including n=0. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_step_ceiling]: the level n epsilon in Federer 2.5.2, p.
    93 *)
Definition real_step_ceiling (R : realType) (e : R) n := n%:R * e.

(** Source for [real_step_ceiling_zero]: the initial truncation level used
    in the sum of Federer 2.5.2, p. 93 *)
Lemma real_step_ceiling_zero (R : realType) (e : R) : real_step_ceiling e 0=0.
Proof. by rewrite /real_step_ceiling mul0r. Qed.

(** Source for [real_step_ceiling_successor]: consecutive epsilon levels in
    Federer 2.5.2, p. 93 *)
Lemma real_step_ceiling_successor (R : realType) (e : R) n :
  real_step_ceiling e n.+1=real_step_ceiling e n+e.
Proof. by rewrite /real_step_ceiling -addn1 natrD mulrDl mul1r. Qed.

(** Source for [real_step_ceiling_difference]: equal layer widths in Federer
    2.5.2, p. 93 *)
Lemma real_step_ceiling_difference (R : realType) (e : R) n :
  real_step_ceiling e n.+1-real_step_ceiling e n=e.
Proof. by rewrite real_step_ceiling_successor addrAC subrr add0r. Qed.

(** Source for [real_step_ceiling_nonnegative]: admissible nonnegative
    ceilings for Federer 2.5.2, p. 93 *)
Lemma real_step_ceiling_nonnegative (R : realType) (e : R) n :
  0 <= e -> 0 <= real_step_ceiling e n.
Proof. move=> he; exact: mulr_ge0 (ler0n _ _) he. Qed.

(** Source for [real_step_ceiling_monotone]: ordered truncation levels in
    Federer 2.5.2, p. 93 *)
Lemma real_step_ceiling_monotone (R : realType) (e : R) n m :
  0 < e -> (n <= m)%N -> real_step_ceiling e n <= real_step_ceiling e m.
Proof. move=> he hnm; by rewrite /real_step_ceiling (ler_pM2r he) ler_nat. Qed.

(** Source for [real_step_ceiling_strict_next]: positive layer width in
    Federer 2.5.2, p. 93 *)
Lemma real_step_ceiling_strict_next (R : realType) (e : R) n :
  0 < e -> real_step_ceiling e n < real_step_ceiling e n.+1.
Proof. move=> he; by rewrite real_step_ceiling_successor ltrDl. Qed.
