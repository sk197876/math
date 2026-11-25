(** Federer (1969), 4.1.14, p. 371: the affine deformation
    of locally Lipschitz maps is locally Lipschitz.
    These supporting linear-coordinate and sum laws follow
    directly from 2.2.7, pp. 63–64. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric
  NormDifferentialUP NormBoundedLinearTopology LipschitzUP LipschitzBasic
  MetricLipschitzComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_local_lipschitz_linear_precompose]: composition
    with a bounded linear coordinate map preserves the original
    relative local Lipschitz condition of 2.2.7, p. 64,
    supporting the affine homotopy of 4.1.14, p. 371. *)
Theorem norm_local_lipschitz_linear_precompose (R : realType)
    (X Y Z : lmodType R) (NX : X -> R) (NY : Y -> R) (NZ : Z -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) (hNZ : is_real_norm NZ)
    (A : set X) (B : set Y) (L : Hom X Y) (f : Y -> Z) :
  norm_bounded_linear NX NY L ->
  (forall x, A x -> B (L x)) ->
  @is_locally_metric_lipschitz R (real_norm_metric_space hNY)
    (real_norm_metric_space hNZ) B f ->
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNZ) A (fun x => f (L x)).
Proof.
move=> hL hImage hF a ha.
have [W [hW [M [hM hFM]]]] := hF (L a) (hImage a ha).
have hContinuous := @norm_bounded_linear_continuous R X Y NX NY hNX hNY L hL.
have hPre : nbhs (a:real_norm_metric_space hNX) (L @^-1` W).
  exact: (hContinuous a _ hW).
have [C [hC hLC]] := hL.
have hBound : @is_metric_lipschitz_bound R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) (A `&` (L @^-1` W)) L C.
  split; first exact: hC.
  move=> x y _ _.
  change (is_true (NY (L x-L y) <= C*NX (x-y))).
  by rewrite -(linB (hom_linear L)); exact: hLC.
have hComposite := @metric_lipschitz_composition_bound R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY)
  (real_norm_metric_space hNZ) (A `&` (L @^-1` W)) (B `&` W)
  L f C M (fun x hx => conj (hImage x hx.1) hx.2) hBound hFM.
exists (L @^-1` W); split; first exact: hPre.
exact: metric_lipschitz_of_bound hComposite.
Qed.

(** Source for [norm_local_lipschitz_add]: addition preserves the
    local distance bounds of Federer 2.2.7, p. 64,
    as used in the affine deformation of 4.1.14, p. 371. *)
Theorem norm_local_lipschitz_add (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : set X) (f g : X -> Y) :
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) A f ->
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) A g ->
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) A (fun x => f x+g x).
Proof.
move=> hF hG a ha.
have [W [hW [L [hL hFL]]]] := hF a ha.
have [Z [hZ [M [hM hGM]]]] := hG a ha.
exists (W `&` Z); split; first exact: filterI hW hZ.
exists (L+M); split; first exact: addr_gt0 hL hM.
split; first exact: addr_ge0 (ltW hL) (ltW hM).
move=> x y [hx [hxW hxZ]] [hy [hyW hyZ]].
change (is_true (NY ((f x+g x)-(f y+g y)) <= (L+M)*NX (x-y))).
have hDifference : (f x+g x)-(f y+g y)=(f x-f y)+(g x-g y).
  by rewrite opprD addrACA.
rewrite hDifference mulrDl.
exact: (le_trans (real_seminorm_triangle hNY.1 _ _)
  (lerD (hFL.2 x y (conj hx hxW) (conj hy hyW))
    (hGM.2 x y (conj hx hxZ) (conj hy hyZ)))).
Qed.
