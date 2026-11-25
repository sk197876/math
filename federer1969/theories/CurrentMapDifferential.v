(** Federer (1969), 4.1.7, p. 359:
    the actual differential in the exterior
    image of the original orienting field.
    This supporting alias uses the sealed
    partial differential of 3.1.1, p. 209,
    and the sealed graph-preserving extension
    of 2.3.2, p. 73. No derivative
    or continuity law is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialSealed
  NormClassOneUP NormRegularity PartialFunctionExtensionSealed InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentMapDifferential.
Variable R:realType.
Variables v n:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:X->Prop.
Variable f:X->Y.

(** Source for [current_map_differential]: an alias
    for the actual original partial Df, with
    a value outside its domain used only
    to type total auxiliary fields, supporting
    Federer 4.1.7, p. 359. The subsequent
    laws retain every point of U. *)
Definition current_map_differential:X->Hom X Y:=
  @PartialFunctionExtension.value X (Hom X Y)
    (@NormDifferential.value R X Y NX NY hNX hNY U f) 0.

(** Source for [current_map_differential_unique]: any
    actual derivative equals this original graph
    value, supporting Federer 4.1.7, p. 359,
    by the exact laws of 3.1.1. *)
Lemma current_map_differential_unique x (L:Hom X Y):
  has_norm_differential NX NY U f x L->current_map_differential x=L.
Proof.
move=>hL.
exact:(@PartialFunctionExtension.laws X (Hom X Y)
  (@NormDifferential.value R X Y NX NY hNX hNY U f) 0 x L
  ((@NormDifferential.laws R X Y NX NY hNX hNY U f x L).2 hL)).
Qed.

(** Source for [current_map_differential_actual]: a
    smooth original map has its actual Df
    at every point of U, supporting
    Federer 4.1.7, p. 359. Smoothness,
    rather than a derivative-field premise,
    supplies existence. *)
Theorem current_map_differential_actual:
  norm_class_all_orders hNX hNY U f->forall x,U x->
    has_norm_differential NX NY U f x (current_map_differential x).
Proof.
move=>hf x hx.
have [D hD]:=(@norm_class_firstP R X Y NX NY hNX hNY U f).1 (hf 1%N).
have hActual:=norm_class_one_differential hD hx.
rewrite (current_map_differential_unique hActual);exact:hActual.
Qed.
End CurrentMapDifferential.
