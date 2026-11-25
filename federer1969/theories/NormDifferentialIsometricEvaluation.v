(** Federer (1969), 3.1.11, pp. 218–219:
    the recursive zero/one-order identifications preserve
    differentiation. This supporting lemma treats any linear
    isometric evaluation into the original value space. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_isometric_evaluation]:
    replacing a value space by an isometrically identified
    copy changes neither the first-order approximation nor
    its domain, supporting D^0 f=f and D^1 f=Df in
    Federer 3.1.11, pp. 218–219. *)
Theorem norm_differential_isometric_evaluation (R : realType)
    (X Z Y : lmodType R) (NX : X->R) (ZN : Z->R) (NY : Y->R)
    (J : Hom Z Y) (hJ : forall z, ZN z=NY (J z))
    (A : X->Prop) (g : X->Z) (a : X) (L : Hom X Z) :
  has_norm_differential NX ZN A g a L <->
  has_norm_differential NX NY A (fun x=>J (g x)) a (hom_comp J L).
Proof.
split=> h; constructor; first exact: norm_differential_interior h.
- have [C [hC hb]] := norm_differential_bounded h.
  exists C; split=> // v; rewrite hom_compE -hJ; exact: hb.
- move=> e he; have [d [hd hb]] := norm_differential_remainder h he.
  exists d; split=> // v hv hs.
  rewrite hom_compE -!linearB -hJ; exact: hb.
- exact: norm_differential_interior h.
- have [C [hC hb]] := norm_differential_bounded h.
  exists C; split=> // v.
  have hh := hb v; by rewrite hom_compE -hJ in hh.
- move=> e he; have [d [hd hb]] := norm_differential_remainder h he.
  exists d; split=> // v hv hs.
  have hh := hb v hv hs; by rewrite hom_compE -!linearB -hJ in hh.
Qed.
