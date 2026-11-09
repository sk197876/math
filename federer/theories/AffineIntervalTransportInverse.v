(** Federer (1969), 3.3.20, pp. 307–308:
    actual interval similarities have local two-sided inverses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge AffineIntervalTransportUP
  AffineIntervalTransportExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [affine_interval_transport_inverse_laws]:
    supporting actual similarity reduction in 3.3.20,
    pp. 307–308. Independently specified forward
    and inverse interval maps cancel on every original
    compact interval. Only exact image laws and
    positive scalar cancellation are used. *)
Lemma affine_interval_transport_inverse_laws (R:realType) (a r:R) M N:
  0<r ->is_affine_interval_transport a r M ->
  is_affine_interval_transport (-a/r) r^-1 N ->cancel M N /\cancel N M.
Proof.
move=>hr hM hN.
have hNZ:r!=0 by rewrite gt_eqF.
have hLeft:(fun x:R=> -a/r+r^-1 * (a+r * x))=id.
  apply:funext=>x;field;by rewrite hNZ.
have hRight:(fun x:R=>a+r * (-a/r+r^-1 * x))=id.
  apply:funext=>x;field;by rewrite hNZ.
split=>S;apply:val_inj.
- rewrite hN hM image_comp.
  change ((fun x:R=> -a/r+r^-1 * (a+r * x)) @` val S=val S).
  by rewrite hLeft image_id.
- rewrite hM hN image_comp.
  change ((fun x:R=>a+r * (-a/r+r^-1 * x)) @` val S=val S).
  by rewrite hRight image_id.
Qed.

(** Source for [affine_interval_transport_inverse_exists]:
    local actual inverse for the interval similarities
    in 3.3.20, pp. 307–308.
    The inverse map remains existential, with exact
    original image and two-sided cancellation laws. *)
Theorem affine_interval_transport_inverse_exists (R:realType) (a r:R) M:
  0<r ->is_affine_interval_transport a r M ->
  exists N,is_affine_interval_transport (-a/r) r^-1 N /\cancel M N /\cancel N M.
Proof.
move=>hr hM.
have hInverse:0<r^-1 by rewrite invr_gt0.
have [N hN]:=affine_interval_transport_exists (-a/r) hInverse.
exists N;split=>//;exact:affine_interval_transport_inverse_laws hr hM hN.
Qed.
