(** Federer (1969), 3.2.10, p. 248: derive the actual
    inverse differential diagram almost everywhere on a coordinate
    piece. Use Rademacher, 3.2.8, and density-one agreement;
    the Jacobian identity is proved, never assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanStackedMap EuclideanLinearMaps EuclideanLinearJacobian EuclideanBlockInverseJacobian
  EuclideanLebesgueDimensions MeasureUP MeasureAlmostUP MeasureAlmostBasic
  NormDifferentialUP NormDifferential PartialFunctionUP LipschitzUP Rademacher
  LipschitzLeftInverseDifferentials DensityDifferentialAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_piece_differential_diagram_almost]:
    the inverse and kernel diagram of Federer 3.2.10,
    p. 248, at almost every point of E. All three
    differential witnesses are actual derivatives. Orthogonality of
    p is unnecessary for this supporting implication, whose remaining
    hypotheses are the coordinate-piece laws and printed Lipschitzness. *)
Theorem coordinate_piece_differential_diagram_almost (R:realType) n k
    (f:inner_metric_space (@euclidean_inner_productP R (n+k))->
      inner_metric_space (@euclidean_inner_productP R n))
    (p:Hom (R_n R (n+k)) (R_n R k))
    (u v:inner_metric_space (@euclidean_inner_productP R (n+k))->
      inner_metric_space (@euclidean_inner_productP R (n+k)))
    (E:set (R_n R (n+k))):
  is_metric_lipschitz setT f ->is_metric_lipschitz setT u ->is_metric_lipschitz setT v ->
  measure_measurable (@euclidean_lebesgue_measure R (n+k)) E ->
  (forall x,E x ->u x=euclidean_block_join (f x,p x) /\ v (u x)=x) ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R (n+k)) E
    [set a|exists (D:Hom (R_n R (n+k)) (R_n R n))
      (T M:Hom (R_n R (n+k)) (R_n R (n+k))),
      has_norm_differential (inner_norm (@euclidean_inner_productP R (n+k)))
        (inner_norm (@euclidean_inner_productP R n)) setT f a D /\
      has_norm_differential (inner_norm (@euclidean_inner_productP R (n+k)))
        (inner_norm (@euclidean_inner_productP R (n+k))) setT u a T /\
      has_norm_differential (inner_norm (@euclidean_inner_productP R (n+k)))
        (inner_norm (@euclidean_inner_productP R (n+k))) setT v (u a) M /\
      cancel T M /\ (forall x,D (M x)=@euclidean_first_block R n k x) /\
      euclidean_linear_jacobian n D=
        euclidean_linear_jacobian k (hom_comp M (@euclidean_last_injection_map R n k))*
        euclidean_linear_jacobian (n+k) T].
Proof.
move=>hf hu hv hE hCoords.
pose X:=R_n R (n+k).
pose NX:=inner_norm (@euclidean_inner_productP R (n+k)).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (n+k)).
pose mu:=@euclidean_lebesgue_measure R (n+k).
have hm:=euclidean_lebesgue_is_measure R (n+k).
have hD:=federer_3_1_6 hf.
have hInv:=(measure_almost_everywhere_on_implication _ _ _).1 (federer_3_2_8 hu hv).
have hEqOn x:E x ->u x=euclidean_stacked_map f p x.
  move=>hx; by rewrite (hCoords x hx).1 euclidean_stacked_join.
have hAgree:=(measure_almost_everywhere_on_implication _ _ _).1
  (measurable_set_differential_agreement_almost hNX hE hEqOn).
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(@measure_almost_everywhere_mono R _ mu hm _ _ _
  (measure_almost_everywhere_and hm hD
    (measure_almost_everywhere_and hm hInv hAgree)))=>a [hDa [hIa hAa]] ha.
have [D hDf]:=hDa.
have [T [M [hTG [hMG hComp]]]]:=hIa (hCoords a ha).2.
have hT:has_norm_differential NX NX setT u a T.
  exact ((norm_differential_graph (inner_norm_real_norm (@euclidean_inner_productP R (n+k)))
    (inner_norm_real_norm (@euclidean_inner_productP R (n+k))) setT u a T).1 hTG).
have hM:has_norm_differential NX NX setT v (u a) M.
  exact ((norm_differential_graph (inner_norm_real_norm (@euclidean_inner_productP R (n+k)))
    (inner_norm_real_norm (@euclidean_inner_productP R (n+k))) setT v (u a) M).1 hMG).
have hStack:T=euclidean_stacked_linear_map D p.
  exact (hAa ha T _ hT (euclidean_stacked_differential p hDf)).
have hTM:cancel T M.
  move=>x; have h:=congr1 (fun F:Hom X X=>F x) hComp.
  exact h.
have hMT:cancel M T.
  move=>y; have [x <-]:=euclidean_injective_surjective (can_inj hTM) y.
  by rewrite hTM.
have hFirst x:@euclidean_first_block R n k (T x)=D x.
  by rewrite hStack euclidean_stacked_linear_value euclidean_stacked_first_block.
have hProjection x:D (M x)=@euclidean_first_block R n k x.
  by rewrite -(hFirst (M x)) hMT.
exists D,T,M; split; first exact hDf.
split; first exact hT.
split; first exact hM.
split; first exact hTM.
split; first exact hProjection.
exact (euclidean_block_inverse_jacobian hTM hProjection).
Qed.
