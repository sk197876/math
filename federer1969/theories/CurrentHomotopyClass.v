(** Federer (1969), 4.1.9, p. 363: the original
    class-infinity convention retains every finite class
    of the same homotopy and the same original domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations CurrentHomotopyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_smooth_homotopy_all_finite]: class
    infinity means every finite class, supporting Federer
    4.1.9, p. 363, by the convention of
    3.1.11, p. 220. All geometric and endpoint
    data remain those of the original given map. *)
Theorem current_smooth_homotopy_all_finite (R:realType) n nu (A:set R)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu):
  @is_smooth_current_homotopy R n nu A U V f g h <->
    forall r,@is_current_homotopy_class R n nu A U V f g h r.
Proof.
split.
- move=>[hGeometry hClass] r;split;[exact:hGeometry|exact:(hClass r)].
- move=>hFinite;split;first exact:(hFinite 0%N).1.
  move=>r;exact:(hFinite r).2.
Qed.
