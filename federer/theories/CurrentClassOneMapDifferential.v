(** Federer (1969), 4.1.9, p. 363: the actual
    differential of the original finite-class homotopy.
    Reuse the sealed partial differential of 3.1.1,
    pp. 209–210, rather than assume a derivative field. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentMapDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentClassOneMapDifferential.
Variable R:realType.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variable U:set X.

(** Source for [current_class_one_map_differential]: a
    class-one map has its actual sealed differential
    at every point of its original domain, supporting
    Federer 4.1.9, p. 363, by 3.1.1,
    pp. 209–210. Full smoothness is unnecessary. *)
Theorem current_class_one_map_differential (f:X->Y):
  norm_class hNX hNY U f 1%N->forall x,U x->
  has_norm_differential NX NY U f x (@current_map_differential R n nu U f x).
Proof.
move=>hf x hx.
have[D hD]:=(@norm_class_firstP R X Y NX NY hNX hNY U f).1 hf.
have hActual:=norm_class_one_differential hD hx.
rewrite (@current_map_differential_unique R n nu U f x (D x) hActual).
exact:hActual.
Qed.

(** Source for [current_map_differential_domain_agreement]:
    equal maps on the actual open U have the same
    differential there, supporting the endpoint identities
    in Federer 4.1.9, p. 363, by the locality
    of 3.1.1, pp. 209–210. No equality outside U
    or derivative hypothesis on the second representative is required. *)
Theorem current_map_differential_domain_agreement (f g:X->Y):
  (forall x,U x->f x=g x)->norm_class hNX hNY U f 1%N->
  forall x,U x->@current_map_differential R n nu U f x=
    @current_map_differential R n nu U g x.
Proof.
move=>hfg hf x hx.
apply:esym;apply:(@current_map_differential_unique R n nu U g x).
apply:(@norm_differential_domain_agreement R X Y NX NY hNX U f g x _ hfg).
exact:(current_class_one_map_differential hf hx).
Qed.
End CurrentClassOneMapDifferential.
