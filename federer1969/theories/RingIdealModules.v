(** Federer (1969), 3.4.7, p. 325: ideals
    of the ambient germ ring are transverse submodules.
    Their intersection with the finite remainder module
    is the submodule used in the printed induction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP RingSubmoduleUP RingScalarRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ideal_restricted_ring_submodule]: the
    original ideal is a module over the transverse
    germ ring, supporting 3.4.7, p. 325. *)
Lemma ideal_restricted_ring_submodule (A B:comNzRingType)
    (embed:{rmorphism A->B}) (I:set B):
  is_commutative_ideal I ->
  @is_ring_submodule A [the lmodType A of (ring_restricted_space embed B^o)] I.
Proof.
move=>hI;constructor.
- exact:commutative_ideal_zero hI.
- exact:commutative_ideal_add hI.
- exact:commutative_ideal_opp hI.
- move=>a x hx;change (I (embed a*x)).
  exact:(@commutative_ideal_mul B I hI (embed a) x hx).
Qed.

(** Source for [ring_submodule_intersection]: M intersect
    I is a submodule, supporting 3.4.7, p. 325. *)
Lemma ring_submodule_intersection (A:nzRingType) (V:lmodType A) (M N:set V):
  is_ring_submodule M ->is_ring_submodule N ->is_ring_submodule (M `&` N).
Proof.
move=>hM hN;constructor.
- split;[exact:ring_submodule_zero hM|exact:ring_submodule_zero hN].
- move=>x y hx hy;split.
  + exact:(@ring_submodule_add A V M hM x y hx.1 hy.1).
  + exact:(@ring_submodule_add A V N hN x y hx.2 hy.2).
- move=>x hx;split.
  + exact:(@ring_submodule_opp A V M hM x hx.1).
  + exact:(@ring_submodule_opp A V N hN x hx.2).
- move=>a x hx;split.
  + exact:(@ring_submodule_scale A V M hM a x hx.1).
  + exact:(@ring_submodule_scale A V N hN a x hx.2).
Qed.

(** Source for [commutative_ideal_difference]: subtraction
    preserves the original ideal in the remainder argument
    of 3.4.7, p. 325. *)
Lemma commutative_ideal_difference (A:comNzRingType) (I:set A)
    (hI:is_commutative_ideal I) x y:I x ->I y ->I (x-y).
Proof.
move=>hx hy;exact:(@commutative_ideal_add A I hI x (-y) hx
  (@commutative_ideal_opp A I hI y hy)).
Qed.
