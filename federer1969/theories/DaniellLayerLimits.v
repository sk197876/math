(** Federer (1969), proof of 2.5.2, p. 93, final paragraph: the two shifted
    truncation sequences increase to f-f_epsilon and f-f_(2epsilon). These
    supporting limit adapters retain finite real pointwise values and use
    the earlier scalar translation law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLayers MonotoneDaniellIntegralUP
  ExtendedRealOrderLimit RealTotalIntegralLimits RealLatticeTruncationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_functions_increase_subtract_fixed]: subtracting the
    fixed initial truncation in Federer 2.5.2, p. 93 This pointwise
    supporting lemma does not assume any lattice membership. *)
Lemma real_functions_increase_subtract_fixed (R : realType) (X : Type)
    (f : nat -> X -> R) (g h : X -> R) :
  real_functions_increase_to f g ->
  real_functions_increase_to (fun n x => (f n x-h x)%R) (fun x => (g x-h x)%R).
Proof.
move=> hi x; split.
- move=> n m hnm; rewrite lee_fin lerD2r.
  have hh := (hi x).1 n m hnm; by move: hh; rewrite lee_fin.
- exact: (@real_order_limit_translate R (fun n => f n x) (g x) (-h x)%R (hi x).2).
Qed.

(** Source for [real_step_layers_increase]: shifted layer limits in Federer
    2.5.2, p. 93 The fixed offset accommodates both n+1 and n+2 in the
    summed inequalities. *)
Lemma real_step_layers_increase (R : realType) (X : Type)
    (f : X -> R) (a e : R) (k : nat) : (0 < e)%R ->
  real_functions_increase_to
    (fun n => real_lattice_layer f a (((n+k)%:R)*e)%R) (real_lattice_tail f a).
Proof.
move=> he; exact: (@real_functions_increase_subtract_fixed R X
  (fun n x => Order.min (f x) (((n+k)%:R)*e)%R) f (fun x => Order.min (f x) a)
  (@real_step_truncations_increase R X f e k he)).
Qed.
