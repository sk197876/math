(** Federer (1969), 4.1.7, p. 358: the
    original locally normal and normal currents
    form vector spaces. Representability uses the
    original finite-gauge criterion; compact support
    uses the already proved smooth-dual image. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentBoundary CurrentCompactSupport
  CurrentIntegrationCriterion CurrentRepresentableLinear NormalCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section NormalCurrentLinear.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation ED := (fun m=>@current_smooth_dual_space R h2 n U hU m).
Local Notation rho := (fun m=>@current_smooth_dual_restriction R h2 n U hU m).
Local Notation localnormal := (@is_locally_normal_current R h2 n U hU).
Local Notation normal := (@is_normal_current R h2 n U hU).

(** Source for [locally_normal_current_zero]: the
    zero current is locally normal in every
    degree, supporting Federer 4.1.7, p. 358. *)
Theorem locally_normal_current_zero m:localnormal (0:C m).
Proof.
case:m=>[|d];split;try exact:represented_current_zero.
- by [].
- change (@is_integration_representable_current R h2 n d U hU
    (@current_boundary R h2 n d U hU (0:C d.+1))).
  rewrite linear0;exact:represented_current_zero.
Qed.

(** Source for [locally_normal_current_linear]: the
    original locally normal class is closed
    under real linear combinations, Federer
    4.1.7, p. 358. *)
Theorem locally_normal_current_linear m c (T S:C m):
  localnormal T->localnormal S->localnormal (c*:T+S).
Proof.
case:m T S=>[|d] T S [hT hBT] [hS hBS].
- split;last by [].
  exact:(@represented_current_linear R h2 n 0 U hU c T S hT hS).
- split;first exact:(@represented_current_linear R h2 n d.+1 U hU c T S hT hS).
  change (@is_integration_representable_current R h2 n d U hU
    (@current_boundary R h2 n d U hU (c*:T+S))).
  rewrite linearP.
  exact:(@represented_current_linear R h2 n d U hU c
    (@current_boundary R h2 n d U hU T) (@current_boundary R h2 n d U hU S) hBT hBS).
Qed.

(** Source for [normal_current_zero]: the zero
    current is normal in every degree,
    supporting Federer 4.1.7, p. 358. *)
Theorem normal_current_zero m:normal (0:C m).
Proof.
split;first exact:locally_normal_current_zero.
apply:(@current_compact_support_image R h2 n m U hU (0:C m)).1.
exists (0:ED m);exact:linear0.
Qed.

(** Source for [normal_current_linear]: the original
    normal class is closed under real linear
    combinations, Federer 4.1.7, p. 358.
    Compactness follows from the exact earlier
    smooth-dual restriction image, without introducing
    a stronger global-support convention. *)
Theorem normal_current_linear m c (T S:C m):
  normal T->normal S->normal (c*:T+S).
Proof.
move=>[hT hKT] [hS hKS];split.
- exact:(@locally_normal_current_linear m c T S hT hS).
- have[A hA]:=(@current_compact_support_image R h2 n m U hU T).2 hKT.
  have[B hB]:=(@current_compact_support_image R h2 n m U hU S).2 hKS.
  apply:(@current_compact_support_image R h2 n m U hU (c*:T+S)).1.
  exists (c*:A+B).
  exact:(eq_trans (linearP (rho m) c A B)
    (congr2 (fun V W:C m=>c*:V+W) hA hB)).
Qed.
End NormalCurrentLinear.
