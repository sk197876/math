(** Federer (1969), 3.3.20, pp. 307–308:
    the actual positive similarities transport original closed intervals. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra ring.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_affine_closed_segment_image]: supporting
    actual original interval similarity in 3.3.20,
    pp. 307–308. Positive scaling gives exactly
    the transformed closed endpoints, including singleton
    and empty segments. No Cantor-set identity is assumed. *)
Lemma positive_affine_closed_segment_image (R:realType) (a r l h:R):
  0<r ->(fun x:R=>a+r * x) @` (`[l,h]:set (real_line_metric R))=
    (`[a+r * l,a+r * h]:set (real_line_metric R)).
Proof.
move=>hr.
have hNZ:r!=0 by rewrite gt_eqF.
have hCancel y:a+r * ((y-a)/r)=y.
  field;by rewrite hNZ.
apply/seteqP;split=>y.
- move=>[x hx <-].
  change (is_true (l<=x<=h)) in hx.
  change (is_true (a+r * l<=a+r * x<=a+r * h)).
  by rewrite !lerD2l !ler_pM2l.
- move=>hy;exists ((y-a)/r);last exact:hCancel y.
  change (is_true (a+r * l<=y<=a+r * h)) in hy.
  have hBounds:=hy.
  rewrite -[y](hCancel y) !lerD2l !ler_pM2l // in hBounds.
Qed.
