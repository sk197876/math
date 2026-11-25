(** Federer (1969), 3.2.28(2), p. 265:
    Q on O(n,m) is Lipschitz, as needed by
    3.2.22. Telescope its actual unit frame
    columns; the Hilbert Hom norm controls each
    changed column by 1.7.9, p. 35. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorFamilyUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP InnerNorm InnerMetric InnerNormalization HilbertFormCompactness OrthogonalMaps RealNormUP
  ExteriorGrading FiniteExteriorPowers ExteriorNorm InnerExteriorPositivity ExteriorHadamardBound
  ExteriorWordMultilinear EuclideanHomInnerCharts EuclideanStiefelInnerSplitting
  EuclideanExteriorWordCoefficient EuclideanExteriorWordSmooth NormMultilinearFamilyLipschitz
  LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_exterior_frame_lipschitz]: the
    Lipschitz hypothesis for the actual Q map in
    Federer 3.2.28(2), p. 265. The explicit
    bound m follows from its unit frame columns;
    the empty degree-zero map has bound zero. *)
Theorem euclidean_exterior_frame_lipschitz (R:realType) m n:
  @is_metric_lipschitz_bound R (inner_metric_space (@euclidean_hom_inner_productP R m n))
    (inner_metric_space (@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m))
    [set g|is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) (hom_as_linear g)]
    (@euclidean_exterior_word_map R m n) m%:R.
Proof.
split; first exact:ler0n.
move=>g h hG hH; rewrite !inner_metric_distanceE.
pose V:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@exterior_inner_productP R (euclidean_two_nonzero R) V
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m).
pose NY:=inner_norm (@exterior_inner_productP R (euclidean_two_nonzero R) V
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m).
pose f:=fun u:{ffun 'I_m->V}=>e_lambda u (ord_tuple m).
pose a:={ffun 'I_m->V}.
pose u:a:=[ffun i=>h (@coordinate_basis R m i)].
pose v:a:=[ffun i=>g (@coordinate_basis R m i)].
pose H:=inner_norm (@euclidean_hom_inner_productP R m n) (g-h).
have hUnit (F:Hom (R_n R m) (R_n R n)) i:
    is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) (hom_as_linear F) ->
    NX (F (@coordinate_basis R m i))= 1.
  move=>hF; rewrite /NX (orthogonal_map_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) hF).
  exact:(@orthonormal_norm1 R (R_n R m) (@euclidean_inner_product R m)
    (@euclidean_inner_productP R m) (Finite.clone 'I_m _) (@coordinate_basis R m)
    (@euclidean_coordinate_orthonormal_family R m) i).
have hU i:NX (u i)<=1 by rewrite /u ffunE (@hUnit h i hH).
have hV i:NX (v i)<=1 by rewrite /v ffunE (@hUnit g i hG).
have hDiff i:NX (v i-u i)<=H.
  rewrite /v /u !ffunE.
  change (NX ((g-h) (@coordinate_basis R m i))<=H).
  exact:euclidean_hom_frame_evaluation_bound.
have hBound z:NY (f z)<=1*\prod_i NX (z i).
  rewrite mul1r; exact:exterior_product_norm_bound.
have hEstimate:=@norm_multilinear_bounded_family_difference R m (fun _=>V)
  (exterior_power V m) (fun _=>NX) NY (fun _=>hNX) hNY f 1 1 H u v
  (@exterior_ordered_word_multilinear R V m) ler01 hBound (lexx 1)
  (inner_norm_nonnegative _ _) hU hV hDiff.
rewrite expr1n !mulr1 mul1r in hEstimate.
have hWord (F:Hom (R_n R m) (R_n R n)):
    f [ffun i=>F (@coordinate_basis R m i)]=euclidean_exterior_word_map F.
  rewrite /f /euclidean_exterior_word_map /euclidean_exterior_word_coefficient.
  congr (e_lambda _ (ord_tuple m)); apply:funext=>i; by rewrite !ffunE.
rewrite /v /u !hWord in hEstimate.
exact hEstimate.
Qed.
