(** Federer (1969), 4.1.24, pp. 380–381: integer
    source combinations remain integer combinations under
    the actual Lipschitz image. The inverse image
    of an additive target subgroup is an additive
    subgroup of the original flat domain. Only
    the sealed image's public laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom TopologicalGroupUP RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces FlatCurrentsUP FlatCurrentUnion
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic
  CurrentFlatPushforwardZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FlatCurrentImageSubgroup.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables d n m:nat.
Local Notation X:=(R_n R d).
Local Notation Y:=(R_n R n).
Variables (Z:set X) (U:set Y).
Hypothesis hZ:forall x,Z x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R d)) Z x.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable f:X->Y.
Hypothesis hImage:forall x,Z x->U (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) Z f.
Local Notation C:=(@current_space R h2 d Z hZ m).
Local Notation D:=(@current_space R h2 n U hU m).
Local Notation Flat:=(@is_flat_current R h2 d m Z hZ).
Local Notation Push:=(@CurrentFlatLipschitzPushforward.value R h2 d n m
  Z U hZ hU f hImage hLocal).
Variable H:set D.
Hypothesis hH:is_subgroup (fun T S:D=>T+S) (fun T=>-T) 0 H.

(** Source for [flat_current_image_subgroup]: the actual
    Lipschitz image takes integer sums and differences
    to integer sums and differences, supporting the
    zero-degree assertion in 4.1.24, pp. 380–381.
    Flat-domain evidence is existential and never
    replaces the independent target subgroup premise. *)
Theorem flat_current_image_subgroup:
  is_subgroup (fun T S:C=>T+S) (fun T=>-T) 0
    [set T:C|exists hT:Flat T,H (Push T hT)].
Proof.
pose hZero:=@flat_current_zero R h2 d m Z hZ.
constructor.
- exists hZero;rewrite (@current_flat_lipschitz_pushforward_zero
    R h2 d n m Z U hZ hU f hImage hLocal hZero).
  exact:subgroup_unit hH.
- move=>T S [hT hPT] [hS hPS].
  pose hCombination:=@flat_current_linear_combination R h2 d m Z hZ 1 T S hT hS.
  have hSum:Flat (T+S) by move:hCombination;rewrite scale1r.
  exists hSum.
  have hEquality:(1:R)*:T+S=T+S by rewrite scale1r.
  have hValue:=@current_flat_lipschitz_pushforward_congruence
    R h2 d n m Z U hZ hU f hImage hLocal
    ((1:R)*:T+S) (T+S) hCombination hSum hEquality.
  rewrite -hValue (@current_flat_lipschitz_pushforward_linear
    R h2 d n m Z U hZ hU f hImage hLocal 1 T S hT hS) scale1r.
  exact:(@TopologicalGroupUP.subgroup_mul D (fun T S:D=>T+S) (fun T=>-T) 0 H hH
    (Push T hT) (Push S hS) hPT hPS).
- move=>T [hT hPT].
  pose hCombination:=@flat_current_linear_combination R h2 d m Z hZ (-1) T 0 hT hZero.
  have hNeg:Flat (-T) by move:hCombination;rewrite scaleN1r addr0.
  exists hNeg.
  have hEquality:(-1:R)*:T+0= -T by rewrite scaleN1r addr0.
  have hValue:=@current_flat_lipschitz_pushforward_congruence
    R h2 d n m Z U hZ hU f hImage hLocal
    ((-1:R)*:T+0) (-T) hCombination hNeg hEquality.
  rewrite -hValue (@current_flat_lipschitz_pushforward_linear
    R h2 d n m Z U hZ hU f hImage hLocal (-1) T 0 hT hZero)
    (@current_flat_lipschitz_pushforward_zero
      R h2 d n m Z U hZ hU f hImage hLocal hZero) scaleN1r addr0.
  exact:(@TopologicalGroupUP.subgroup_inv D (fun T S:D=>T+S) (fun T=>-T) 0 H hH
    (Push T hT) hPT).
Qed.
End FlatCurrentImageSubgroup.
