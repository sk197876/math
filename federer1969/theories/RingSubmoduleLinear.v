(** Federer (1969), 3.4.7, p. 325: linear
    images and inverse images in the finite-module argument.
    These supporting laws use the independent submodule interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingSubmoduleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ring_submodule_linear_preimage]: inverse
    images under module homomorphisms are submodules, supporting
    the finite-module assertion of 3.4.7, p. 325. *)
Lemma ring_submodule_linear_preimage (A:nzRingType) (V W:lmodType A)
    (f:{linear V->W}) (N:set W):
  is_ring_submodule N ->is_ring_submodule (f @^-1` N).
Proof.
move=>hN;constructor.
- change (N (f 0));rewrite linear0;exact:ring_submodule_zero hN.
- move=>x y hx hy;change (N (f (x+y)));rewrite linearD.
  exact:(@ring_submodule_add A W N hN _ _ hx hy).
- move=>x hx;change (N (f (-x)));rewrite linearN.
  exact:(@ring_submodule_opp A W N hN _ hx).
- move=>a x hx;change (N (f (a*:x)));rewrite linearZ.
  exact:(@ring_submodule_scale A W N hN a _ hx).
Qed.

(** Source for [ring_submodule_linear_image]: images
    under module homomorphisms are submodules, supporting the
    finite-module assertion of 3.4.7, p. 325. *)
Lemma ring_submodule_linear_image (A:nzRingType) (V W:lmodType A)
    (f:{linear V->W}) (N:set V):
  is_ring_submodule N ->is_ring_submodule (f @` N).
Proof.
move=>hN;constructor.
- exists 0;first exact:ring_submodule_zero hN.
  exact:linear0.
- move=>_ _ [x hx <-] [y hy <-];exists (x+y).
  + exact:(@ring_submodule_add A V N hN _ _ hx hy).
  + exact:linearD.
- move=>_ [x hx <-];exists (-x).
  + exact:(@ring_submodule_opp A V N hN _ hx).
  + exact:linearN.
- move=>a _ [x hx <-];exists (a*:x).
  + exact:(@ring_submodule_scale A V N hN a _ hx).
  + exact:linearZ.
Qed.

(** Source for [ring_submodule_difference]: subtraction
    remains in the original module, supporting 3.4.7, p. 325. *)
Lemma ring_submodule_difference (A:nzRingType) (V:lmodType A) (N:set V)
    (hN:is_ring_submodule N) x y:N x ->N y ->N (x-y).
Proof.
move=>hx hy;exact:(@ring_submodule_add A V N hN x (-y) hx
  (@ring_submodule_opp A V N hN y hy)).
Qed.
