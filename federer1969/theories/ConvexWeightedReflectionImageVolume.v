(** A weighted scalar-row connection for the section
    comparison in Federer (1969), 3.2.45,
    pp. 279–280. Reuse the original
    reflection, opaque axis chart, determinant and
    registered Fubini volume laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric InnerConvex OrthonormalFamilies UnitNormalGeometry EuclideanCoordinateSplit
  EuclideanVectorHeadAxis EuclideanHeadScaledVolume EuclideanHeadScaleCoordinates
  EuclideanLinearMaps EuclideanLebesgueDimensions EuclideanLebesgueDeterminant ConvexLinearImageHeadSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_weighted_reflection_image_volume]:
    supporting weighted extension of the scalar-row
    connection for Federer 3.2.45,
    pp. 279–280. If a+b=1
    and Lx=a x+b rho_u(x), an
    actual orthogonal target chart leaves one
    changing row. Scale only the two
    original head rows by a and b,
    preserving their common tails. The existing
    scalar-row Fubini estimate and exact determinant
    law give the absolute scalar factors.
    The relation on L is an independently
    stated coordinate equation, not the desired
    volume inequality. No unit-normal hypothesis is
    required here; its later averaging application
    uses a unit normal for reflection invariance.
    Empty and thin compact convex sources remain. *)
Theorem convex_weighted_reflection_image_volume (R : realType) n m
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (F : {linear R_n R n -> R_n R m.+1}) (u : R_n R n) (a b : R)
    (L : {linear R_n R n -> R_n R n}) :
  compact K -> is_inner_convex K -> a+b= 1 ->
  (forall x, L x=a*:x+b*:normal_reflection (@euclidean_inner_productP R n) u x) ->
  (euclidean_lebesgue_measure m.+1 ((fun x => F (L x)) @` K) <=
    (`|a|)%:E*euclidean_lebesgue_measure m.+1 (F @` K)+
    (`|b|)%:E*euclidean_lebesgue_measure m.+1
      ((fun x => F (normal_reflection (@euclidean_inner_productP R n) u x)) @` K))%E.
Proof.
move=> hCompact hConvex hSum hL.
pose hB := @euclidean_inner_productP R n.
pose rho : {linear R_n R n -> R_n R n} :=
  GRing.Linear.clone _ _ _ _ (normal_reflection hB u) _.
have [T [hT hDirectionTail]] := @euclidean_vector_head_axis_exists R m (F u).
pose A := linear_comp T F.
pose G := linear_comp A rho.
pose M := linear_comp A L.
pose Da := @euclidean_diagonal_map R m.+1 (fun i => if i==ord0 then a else 1).
pose Db := @euclidean_diagonal_map R m.+1 (fun i => if i==ord0 then b else 1).
pose Fa := linear_comp Da A.
pose Gb := linear_comp Db G.
have hDirection i : A u (lift ord0 i)= 0.
  have h := congr1 (fun z : R_n R m => z i) hDirectionTail.
  by rewrite /coordinate_tail !ffunE in h.
have hTailG x : coordinate_tail (G x)=coordinate_tail (A x).
  apply/ffunP=> i; rewrite /coordinate_tail !ffunE.
  change ((A (normal_reflection hB u x)) (lift ord0 i)=A x (lift ord0 i)).
  by rewrite /normal_reflection linearB linearZ !ffunE hDirection ?scaler0 ?mulr0 subr0.
have hRelation x : M x=a*:A x+b*:G x.
  have h := congr1 A (hL x).
  by rewrite linearD !linearZ in h.
have hTailM x : coordinate_tail (M x)=coordinate_tail (A x).
  apply/ffunP=> i; rewrite /coordinate_tail !ffunE.
  have h := congr1 (fun z : R_n R m.+1 => z (lift ord0 i)) (hRelation x).
  rewrite !ffunE in h.
  have hG := congr1 (fun z : R_n R m => z i) (hTailG x).
  rewrite /coordinate_tail !ffunE in hG.
  rewrite hG in h.
  change (M x (lift ord0 i)=a*A x (lift ord0 i)+b*A x (lift ord0 i)) in h.
  by rewrite -mulrDl hSum mul1r in h.
have hTailFa x : coordinate_tail (Fa x)=coordinate_tail (A x).
  exact: euclidean_head_scale_tail.
have hTailGb x : coordinate_tail (Gb x)=coordinate_tail (Fa x).
  rewrite /Gb /linear_comp /= euclidean_head_scale_tail hTailG hTailFa; reflexivity.
have hTailMFa x : coordinate_tail (M x)=coordinate_tail (Fa x).
  by rewrite hTailM hTailFa.
have hHead x : coordinate_head (M x)=coordinate_head (Fa x)+coordinate_head (Gb x).
  have h := congr1 (fun z : R_n R m.+1 => coordinate_head z) (hRelation x).
  rewrite /coordinate_head !ffunE in h.
  rewrite /Fa /Gb /linear_comp /= !euclidean_head_scale_head.
  exact h.
have hVolume := @convex_linear_image_head_sum_volume R n m K Fa Gb M
  hCompact hConvex hTailGb hTailMFa hHead.
have hScaled (c : R) (J : {linear R_n R n -> R_n R m.+1}) :
    euclidean_lebesgue_measure m.+1
      ((linear_comp (@euclidean_diagonal_map R m.+1 (fun i => if i==ord0 then c else 1)) J) @` K)=
    ((`|c|)%:E*euclidean_lebesgue_measure m.+1 (J @` K))%E.
  change (euclidean_lebesgue_measure m.+1
    (((@euclidean_diagonal_map R m.+1 (fun i => if i==ord0 then c else 1)) \o J) @` K)=
    ((`|c|)%:E*euclidean_lebesgue_measure m.+1 (J @` K))%E).
  by rewrite -image_comp euclidean_head_scaled_volume.
have hPreserve (J : {linear R_n R n -> R_n R m.+1}) :
    euclidean_lebesgue_measure m.+1 ((linear_comp T J) @` K)=euclidean_lebesgue_measure m.+1 (J @` K).
  change (euclidean_lebesgue_measure m.+1 ((T \o J) @` K)=euclidean_lebesgue_measure m.+1 (J @` K)).
  rewrite -image_comp euclidean_lebesgue_linear_image (euclidean_orthogonal_det hT).
  exact: mul1e.
have hM := hPreserve (linear_comp F L).
have hA := hPreserve F.
have hG := hPreserve (linear_comp F rho).
rewrite (hScaled a A) (hScaled b G) hM hA hG in hVolume.
exact hVolume.
Qed.
