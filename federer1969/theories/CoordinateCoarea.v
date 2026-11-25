(** Federer (1969), 3.2.10, p. 248: coarea on every
    measurable subset of a Borel coordinate inverse piece,
    and the exact fibre identity for every target point.
    Erratum p. 4 corrects book p. 248 line 21 to
    Lebesgue degree m-n and line 25 to Hausdorff degree m-n. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanLebesgueDimensions CoordinateInverseCoverUP
  CoordinateInverseFibres CoordinatePieceCoarea EuclideanTargetJacobianMeasurable
  HausdorffMeasure MappingMultiplicity MeasureUP MeasureIntegralUP MeasureSubsetIntegral
  PartialFunctionBasic ExtendedRealOrderTopology LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_2_10]: the integral equality
    in Federer 3.2.10, p. 248. Retain the printed
    m>n, Lipschitz f and measurable B subset E, where
    E has exactly the coordinate-piece laws of 3.2.9.
    Both actual integrals exist, possibly with infinite value;
    the target-degree Jacobian keeps its differential domain. *)
Theorem federer_3_2_10 (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (E:set (R_n R m)):
  (n<m)%N ->is_metric_lipschitz setT f ->is_coordinate_inverse_piece f E ->
  forall B,measure_measurable (@euclidean_lebesgue_measure R m) B ->B `<=` E ->
  exists a,is_measure_subset_integral (@euclidean_lebesgue_measure R m) B
      (extended_euclidean_target_jacobian f) a /\
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (partial_function_total (fun y=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f B y)
          :extended_real_line R))) a.
Proof.
move=>hnm hf hPiece B hB hBE.
have hNM:(n<=m)%N:=ltnW hnm.
have [k he]:exists k:nat,m=(n+k)%N.
  exists (m-n)%N; by rewrite subnKC.
subst m.
rewrite /is_coordinate_inverse_piece addKn in hPiece.
have [_ [p [_ [u [v [hu [hv hCoords]]]]]]]:=hPiece.
have hBParts x:B x ->u x=euclidean_block_join (f x,hom_of_linear p x) /\ v (u x)=x.
  move=>hx; exact (hCoords x (hBE x hx)).
rewrite addKn.
exact (coordinate_piece_coarea hf hu hv hB hBParts).
Qed.

(** Source for [federer_3_2_10_fibre_identity]: the final
    set identity in the statement of Federer 3.2.10,
    p. 248, with the actual p,u,v of a coordinate
    piece. The supporting identity holds in every dimension
    and requires only their exact laws on E; every y,
    including empty fibres, is retained without an exceptional set. *)
Theorem federer_3_2_10_fibre_identity (R:realType) m n
    (f:R_n R m->R_n R n) (E:set (R_n R m))
    (p:{linear R_n R m->R_n R (m-n)})
    (u:R_n R m->R_n R (n+(m-n))) (v:R_n R (n+(m-n))->R_n R m):
  (forall x,E x ->u x=euclidean_block_join (f x,p x) /\ v (u x)=x) ->
  forall y,mapping_fibre f E y=
    (fun z=>v (euclidean_block_join (y,z))) @` (p @` mapping_fibre f E y).
Proof. exact:coordinate_inverse_fibre_image. Qed.
