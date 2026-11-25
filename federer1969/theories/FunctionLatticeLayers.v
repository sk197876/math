(** Federer (1969), proof of 2.5.2, p. 93: differences of two nonnegative
    truncations, used in the epsilon layer estimates. The lemmas allow
    arbitrary 0 <= a <= b before specialising to consecutive multiples of
    epsilon. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP FunctionLatticeRamp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_lattice_layer]: the difference f_b-f_a underlying the
    epsilon layers in Federer 2.5.2, p. 93 *)
Definition real_lattice_layer (R : realType) (X : Type) (f : X -> R) (a b : R) x :=
  Order.min (f x) b-Order.min (f x) a.

(** Source for [real_lattice_layer_member]: positivity and lattice
    membership of each layer in Federer 2.5.2, p. 93 *)
Lemma real_lattice_layer_member (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (f : X -> R) a b :
  L f -> 0 <= a -> a <= b -> positive_function_lattice L (real_lattice_layer f a b).
Proof.
move=> hf ha hab.
have hb : 0 <= b := le_trans ha hab.
have hfa := function_lattice_truncation hL ha hf.
have hfb := function_lattice_truncation hL hb hf.
have horder : function_le (fun x => Order.min (f x) a) (fun x => Order.min (f x) b).
  move=> x; exact: real_minimum_ceiling_monotone hab.
split; first exact: (@function_lattice_ordered_difference R X L hL
  (fun x => Order.min (f x) a) (fun x => Order.min (f x) b) hfa hfb horder).
by move=> x; rewrite /real_lattice_layer subr_ge0; exact: horder.
Qed.

(** Source for [real_lattice_layer_bound]: the upper bound epsilon for
    consecutive layers in Federer 2.5.2, p. 93 This supporting form gives
    b-a for any ordered truncation endpoints. *)
Lemma real_lattice_layer_bound (R : realType) (X : Type) (f : X -> R) a b x :
  a <= b -> real_lattice_layer f a b x <= b-a.
Proof.
move=> hab; rewrite /real_lattice_layer.
case: (boolP (f x <= a))=> hfa.
- have hfb := le_trans hfa hab.
  by rewrite (min_l hfa) (min_l hfb) subrr subr_ge0.
- case: (boolP (f x <= b))=> hfb.
  + have haf : a <= f x by apply: ltW; move: hfa; rewrite -ltNge.
    by rewrite (min_r haf) (min_l hfb) lerD2r.
  + have hbf : b <= f x by apply: ltW; move: hfb; rewrite -ltNge.
    have haf := le_trans hab hbf.
    by rewrite (min_r haf) (min_r hbf).
Qed.

(** Source for [real_lattice_layer_zero]: the layer vanishes where f <= a in
    Federer 2.5.2, p. 93 *)
Lemma real_lattice_layer_zero (R : realType) (X : Type) (f : X -> R) a b x :
  a <= b -> f x <= a -> real_lattice_layer f a b x=0.
Proof.
move=> hab hfa; by rewrite /real_lattice_layer (min_l hfa) (min_l (le_trans hfa hab)) subrr.
Qed.

(** Source for [real_lattice_layer_full]: the layer equals b-a where f >= b
    in Federer 2.5.2, p. 93 *)
Lemma real_lattice_layer_full (R : realType) (X : Type) (f : X -> R) a b x :
  a <= b -> b <= f x -> real_lattice_layer f a b x=b-a.
Proof. move=> hab hbf; by rewrite /real_lattice_layer (min_r hbf) (min_r (le_trans hab hbf)). Qed.

(** Source for [real_lattice_layer_telescope]: telescoping adjacent layers
    in the summation display of Federer 2.5.2, p. 93 The algebraic identity
    itself needs no order or sign assumptions. *)
Lemma real_lattice_layer_telescope (R : realType) (X : Type) (f : X -> R) a b c x :
  real_lattice_layer f a b x+real_lattice_layer f b c x=real_lattice_layer f a c x.
Proof. by rewrite /real_lattice_layer addrCA addrAC subrr add0r. Qed.

(** Source for [real_lattice_layer_same]: empty layer in the telescoping sum
    of Federer 2.5.2, p. 93 This supports the zero-term base case of the
    formal finite induction. *)
Lemma real_lattice_layer_same (R : realType) (X : Type) (f : X -> R) a :
  real_lattice_layer f a a=(fun _ : X => 0).
Proof. by apply: funext=> x; rewrite /real_lattice_layer subrr. Qed.

(** Source for [real_lattice_layer_from_zero]: f_0=0 for nonnegative f in
    the summation display of Federer 2.5.2, p. 93 *)
Lemma real_lattice_layer_from_zero (R : realType) (X : Type) (f : X -> R) b :
  function_nonnegative f -> real_lattice_layer f 0 b=(fun x => Order.min (f x) b).
Proof. move=> hf; by apply: funext=> x; rewrite /real_lattice_layer (min_r (hf x)) subr0. Qed.

(** Source for [real_lattice_tail]: the difference f-f_epsilon in the final
    limiting paragraph of Federer 2.5.2, p. 93 *)
Definition real_lattice_tail (R : realType) (X : Type) (f : X -> R) (a : R) x :=
  f x-Order.min (f x) a.

(** Source for [real_lattice_tail_member]: positivity and lattice membership
    of f-f_epsilon in Federer 2.5.2, p. 93 A nonnegative cutoff suffices
    even if f itself has negative values. *)
Lemma real_lattice_tail_member (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (f : X -> R) a :
  L f -> 0 <= a -> positive_function_lattice L (real_lattice_tail f a).
Proof.
move=> hf ha; have hmin := function_lattice_truncation hL ha hf.
have hle : function_le (fun x => Order.min (f x) a) f by move=> x; rewrite ge_min lexx.
split; first exact: (@function_lattice_ordered_difference R X L hL
  (fun x => Order.min (f x) a) f hmin hf hle).
by move=> x; rewrite /real_lattice_tail subr_ge0; exact: hle.
Qed.
