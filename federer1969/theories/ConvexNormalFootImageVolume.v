(** A scalar-row Fubini connection for the sharp comparison
    in Federer (1969), 3.2.45, pp. 279–280.
    This specializes the registered row-volume inequality;
    it does not assume mixed-volume monotonicity. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric InnerConvex InnerProductUP OrthonormalFamilies UnitNormalGeometry
  EuclideanCoordinateSplit EuclideanVectorHeadAxis EuclideanHeadScaledVolume
  EuclideanLinearMaps EuclideanLebesgueDimensions EuclideanLebesgueDeterminant
  ConvexLinearImageHeadSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_normal_foot_image_volume]: supporting
    reflected-volume connection for the sharp projection
    comparison in Federer 3.2.45, pp. 279–280.
    Twice the actual projected volume of a compact
    convex body's normal foot is at most the
    sum of its original and reflected projected
    volumes. The proved scalar-row Fubini inequality
    applies after an original orthogonal target chart
    moves the single changed direction onto the
    head axis. Only that scalar row is doubled;
    the original determinant law gives its factor two.
    Empty and thin bodies and a vanishing projected
    direction remain. No unit-normal premise is needed
    for this algebraic connection; reflection invariance
    in its later application requires a unit normal. *)
Theorem convex_normal_foot_image_volume (R : realType) n m
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (F : {linear R_n R n -> R_n R m.+1}) (u : R_n R n) :
  compact K -> is_inner_convex K ->
  ((2:R)%:E * euclidean_lebesgue_measure m.+1
      ((fun x => F (normal_foot (@euclidean_inner_productP R n) u x)) @` K) <=
    euclidean_lebesgue_measure m.+1 (F @` K) +
    euclidean_lebesgue_measure m.+1
      ((fun x => F (normal_reflection (@euclidean_inner_productP R n) u x)) @` K))%E.
Proof.
move=> hCompact hConvex.
pose hB := @euclidean_inner_productP R n.
pose P : {linear R_n R n -> R_n R n} :=
  GRing.Linear.clone _ _ _ _ (normal_foot hB u) _.
pose rho : {linear R_n R n -> R_n R n} :=
  GRing.Linear.clone _ _ _ _ (normal_reflection hB u) _.
have [T [hT hTailDirection]] := @euclidean_vector_head_axis_exists R m (F u).
pose A := linear_comp T F.
pose G := linear_comp A rho.
pose M := linear_comp A P.
pose D := @euclidean_diagonal_map R m.+1 (fun i => if i==ord0 then 2 else 1).
pose H := linear_comp D M.
have hTailAU : @coordinate_tail R m (A u)= 0 := hTailDirection.
have hDirection i : A u (lift ord0 i)= 0.
  have h := congr1 (fun z : R_n R m => z i) hTailAU.
  by rewrite /coordinate_tail !ffunE in h.
have hTailG x : coordinate_tail (G x)=coordinate_tail (A x).
  apply/ffunP=> i; rewrite /coordinate_tail !ffunE.
  change ((A (normal_reflection hB u x)) (lift ord0 i) = A x (lift ord0 i)).
  by rewrite /normal_reflection linearB linearZ !ffunE hDirection ?mulr0 ?scaler0 subr0.
have hTailM x : coordinate_tail (M x)=coordinate_tail (A x).
  apply/ffunP=> i; rewrite /coordinate_tail !ffunE.
  change ((A (normal_foot hB u x)) (lift ord0 i) = A x (lift ord0 i)).
  by rewrite /normal_foot linearB linearZ !ffunE hDirection ?mulr0 ?scaler0 subr0.
have hTailD y : coordinate_tail (D y)=coordinate_tail y.
  apply/ffunP=> i.
  by rewrite /coordinate_tail /D /euclidean_diagonal_map /euclidean_diagonal !ffunE lift_eqF mul1r.
have hTailH x : coordinate_tail (H x)=coordinate_tail (A x).
  exact: eq_trans (hTailD (M x)) (hTailM x).
have hMidpoint x : (2:R)*:M x=A x+G x.
  have hSource : (2:R)*:normal_foot hB u x=x+normal_reflection hB u x.
    have hDouble : (2:R)*:x=x+x.
      change ((1+1:R)*:x=x+x); by rewrite scalerDl !scale1r.
    by rewrite /normal_foot /normal_reflection scalerBr scalerA hDouble addrA.
  have h := congr1 A hSource.
  rewrite linearZ linearD in h; exact h.
have hHead x : coordinate_head (H x)=(coordinate_head (A x)+coordinate_head (G x)).
  have h := congr1 (fun z : R_n R m.+1 => coordinate_head z) (hMidpoint x).
  rewrite /coordinate_head !ffunE in h.
  rewrite /coordinate_head /H /linear_comp /= /D /euclidean_diagonal_map /euclidean_diagonal !ffunE eqxx; exact h.
have hVolume := @convex_linear_image_head_sum_volume R n m K A G H
  hCompact hConvex hTailG hTailH hHead.
have hScaled : euclidean_lebesgue_measure m.+1 (H @` K) =
    ((2:R)%:E * euclidean_lebesgue_measure m.+1 (M @` K))%E.
  change (euclidean_lebesgue_measure m.+1 ((D \o M) @` K) =
    ((2:R)%:E * euclidean_lebesgue_measure m.+1 (M @` K))%E).
  rewrite -image_comp /D (@euclidean_head_scaled_volume R m 2 (M @` K)).
  by rewrite (ger0_norm (ler0n R 2)).
have hPreserve (L : {linear R_n R n -> R_n R m.+1}) :
    euclidean_lebesgue_measure m.+1 ((linear_comp T L) @` K)=
      euclidean_lebesgue_measure m.+1 (L @` K).
  change (euclidean_lebesgue_measure m.+1 ((T \o L) @` K)=
    euclidean_lebesgue_measure m.+1 (L @` K)).
  rewrite -image_comp euclidean_lebesgue_linear_image (euclidean_orthogonal_det hT).
  exact: mul1e.
have hMValue : euclidean_lebesgue_measure m.+1 (M @` K)=
    euclidean_lebesgue_measure m.+1 ((linear_comp F P) @` K).
  exact (hPreserve (linear_comp F P)).
have hGValue : euclidean_lebesgue_measure m.+1 (G @` K)=
    euclidean_lebesgue_measure m.+1 ((linear_comp F rho) @` K).
  exact (hPreserve (linear_comp F rho)).
have hAValue := hPreserve F.
rewrite hScaled hMValue hGValue hAValue in hVolume.
exact hVolume.
Qed.
