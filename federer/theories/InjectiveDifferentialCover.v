(** Federer (1969), 3.2.2, p. 242: countable Borel
    cover of the injective differentiability locus with distortion
    arbitrarily close to one. The cover is proved from its
    abstract laws and assumes no decomposition theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormMetric NormClassOneUP NormClassZeroWhole
  FiniteNormMetricPolish SeparableClosedCover TopologicalBorel BorelFamilyBasic
  EuclideanHomOperator CountableLinearAutomorphismApproximation
  LinearModelRemainderBounds LinearModelLocus LinearModelLocusBorel
  LinearModelPieceEstimates InjectiveDifferentialPieceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [injective_differential_borel_cover_exists]: the
    full covering assertion and all four estimates of Federer
    3.2.2, p. 242. Intersect Z(s,i) with a countable
    closed cover of diameter at most 1/(i+1). The polar
    factorization uses the isometry O(n,m), corrected by erratum
    p. 4, book p. 242 line 23. *)
Theorem injective_differential_borel_cover_exists (R:realType) m n
    (f:R_n R m->R_n R n) (lambda:R):
  norm_class_zero (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  1<lambda -> exists G,is_injective_differential_cover f lambda G.
Proof.
move=>hf hl.
have [e [he [hmargin1 hmargin2]]]:=bilipschitz_margin_exists hl.
have [S [hCount [hInj hDense]]]:=@countable_linear_automorphism_approximation R m.
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose E:=real_norm_metric_space hNX.
have [D [hD hDdense]]:=@finite_norm_metric_separable R (R_n R m)
  (inner_norm (@euclidean_inner_productP R m)) hNX m (@coordinate_basis R m) (@coordinate_basisP R m).
have hex i:exists F:nat->set E,
    (forall j,closed (F j) /\ F j !=set0 /\ F j `<=` setT /\
      forall a b,F j a -> F j b -> mdist a b<=(i.+1%:R:R)^-1) /\
    setT=\bigcup_j F j.
  apply:(@separable_closed_small_cover R E D setT (i.+1%:R:R)^-1 hD hDdense (@closedT E)).
  - by exists (0:R_n R m).
  - by rewrite invr_gt0 ltr0n.
have [F hF]:=choice hex.
pose J:=S `*` (@setT (nat*nat)).
pose piece (p:Hom (R_n R m) (R_n R m)*(nat*nat)):
    set E:=linear_model_locus f p.1 lambda e p.2.1 `&` F p.2.1 p.2.2.
pose G:=piece @` J.
have hJ:countable J by apply:countableX=>//; exact:countableP.
have hPiece p:J p -> is_injective_differential_piece f lambda (piece p).
  move=>[hs _].
  apply:(@linear_model_small_piece R m n f p.1 lambda e p.2.1 (piece p) hl he (hInj p.1 hs)).
  - exact (borel_family_binary_intersection (borel_sets_family E)
      (linear_model_locus_borel p.1 lambda e p.2.1 hf)
      (closed_borel_set ((hF p.2.1).1 p.2.2).1)).
  - by move=>a [ha _].
  - move=>a b [_ ha] [_ hb]; exact (((hF p.2.1).1 p.2.2).2.2.2 a b ha hb).
exists G; split.
- exact (sub_countable (card_image_le piece J) hJ).
split.
- apply/seteqP; split=>a.
  + move=>[A [p hp <-] ha]; exact ((hPiece p hp).2.1 a ha).
  + move=>[T [hT hTI]].
    have [s [hs [i hi]]]:=linear_model_locus_covers_injective hInj hDense hl he hmargin1 hmargin2 hT hTI.
    have hcover:(\bigcup_j F i j) a by rewrite -(hF i).2.
    have [j _ hj]:=hcover.
    exists (piece (s,(i,j))).
    * exists (s,(i,j)); last by [].
      by split.
    * by split.
- by move=>A [p hp <-]; exact (hPiece p hp).
Qed.

(** Source for [federer_3_2_2]: Federer 3.2.2, p. 242,
    with exactly the printed continuity and lambda>1 hypotheses,
    arbitrary source and target dimensions, and the erratum-
    corrected polar isometry direction in the existence proof. *)
Theorem federer_3_2_2 (R:realType) m n (f:R_n R m->R_n R n) (lambda:R):
  continuous (fun x:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m))=>
    (f x:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))) ->
  1<lambda -> exists G,is_injective_differential_cover f lambda G.
Proof.
move=>hf hl; apply:injective_differential_borel_cover_exists hl.
exact (@norm_continuous_whole_class_zero R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) f hf).
Qed.
