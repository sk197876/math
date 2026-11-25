(** Federer (1969), 4.1.12, p. 367: the
    maximum of the two original finite seminorms is
    a seminorm. This supporting order argument retains
    both zero seminorms and arbitrary vector spaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_seminorm_maximum]: the maximum
    in the displayed flat-form definition is a seminorm,
    supporting Federer 4.1.12, p. 367. It requires
    neither positive definiteness nor finite dimension. *)
Lemma real_seminorm_maximum (R:realType) (E:lmodType R)
    (p q:E->R) (hp:is_real_seminorm p) (hq:is_real_seminorm q):
  is_real_seminorm (fun x=>Num.max (p x) (q x)).
Proof.
constructor.
- move=>x;by rewrite le_max (real_seminorm_nonnegative hp x).
- move=>c x;rewrite (real_seminorm_scale hp) (real_seminorm_scale hq).
  case:(leP (p x) (q x))=>hOrder.
  + by rewrite (max_idPr (ler_wpM2l (normr_ge0 c) hOrder)).
  + by rewrite (max_idPl (ler_wpM2l (normr_ge0 c) (ltW hOrder))).
- move=>x y;rewrite ge_max;apply/andP;split.
  + apply:(le_trans (real_seminorm_triangle hp x y));apply:lerD;
      by rewrite le_max lexx.
  + apply:(le_trans (real_seminorm_triangle hq x y));apply:lerD;
      by rewrite le_max lexx orbT.
Qed.
