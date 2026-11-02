(** Federer (1969), proof of 2.5.2, p. 93: the cutoff (b-a)^-1
    (min(f,b)-min(f,a)), for 0 <= a < b. These are lattice and
    scalar-algebra facts, prior to measurability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_minimum_ceiling_monotone]: supporting order between the
    two truncations in Federer 2.5.2, p. 93 *)
Lemma real_minimum_ceiling_monotone (R : realType) (r a b : R) :
  a <= b -> Order.min r a <= Order.min r b.
Proof.
move=> hab; rewrite le_min; apply/andP; split; first by rewrite ge_min lexx.
apply: le_trans (_ : a <= b)=> //; by rewrite ge_min lexx orbT.
Qed.

(** Source for [real_lattice_ramp]: direct cutoff h in Federer 2.5.2, p. 93,
    first displayed definition *)
Definition real_lattice_ramp (R : realType) (X : Type) (f : X -> R) (a b : R) x :=
  (b-a)^-1 * (Order.min (f x) b-Order.min (f x) a).

(** Source for [real_lattice_ramp_member]: the cutoff belongs to L+ in
    Federer 2.5.2, p. 93 Only the printed lattice operations, including
    nonnegative truncation constants, are used. *)
Lemma real_lattice_ramp_member (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (f : X -> R) a b :
  L f -> 0 <= a -> a < b -> positive_function_lattice L (real_lattice_ramp f a b).
Proof.
move=> hf ha hab.
have hb : 0 <= b := le_trans ha (ltW hab).
have hfa := function_lattice_truncation hL ha hf.
have hfb := function_lattice_truncation hL hb hf.
have horder : function_le (fun x => Order.min (f x) a) (fun x => Order.min (f x) b).
  move=> x; exact: real_minimum_ceiling_monotone (ltW hab).
have hd := function_lattice_ordered_difference hL hfa hfb horder.
have hp : 0 <= (b-a)^-1 by rewrite invr_ge0 subr_ge0; exact: ltW hab.
split; first exact: (@function_lattice_scale R X L hL (b-a)^-1
  (fun x => Order.min (f x) b-Order.min (f x) a) hp hd).
move=> x; apply: mulr_ge0 hp _; rewrite subr_ge0; exact: horder.
Qed.

(** Source for [real_lattice_ramp_zero]: h vanishes on {f <= a} in Federer
    2.5.2, p. 93 *)
Lemma real_lattice_ramp_zero (R : realType) (X : Type) (f : X -> R) a b x :
  a <= b -> f x <= a -> real_lattice_ramp f a b x=0.
Proof.
move=> hab hfa; rewrite /real_lattice_ramp (min_l hfa) (min_l (le_trans hfa hab)) subrr mulr0.
by [].
Qed.

(** Source for [real_lattice_ramp_one]: h equals one on {f >= b} in Federer
    2.5.2, p. 93 *)
Lemma real_lattice_ramp_one (R : realType) (X : Type) (f : X -> R) a b x :
  a < b -> b <= f x -> real_lattice_ramp f a b x= 1.
Proof.
move=> hab hbf.
have hd : b-a != 0 by rewrite gt_eqF // subr_gt0.
by rewrite /real_lattice_ramp (min_r hbf) (min_r (le_trans (ltW hab) hbf)) mulVf.
Qed.
