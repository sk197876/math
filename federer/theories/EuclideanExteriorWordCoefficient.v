(** Federer (1969), 3.2.28(2), printed p. 264: the map
    g to its m-th exterior power is polynomial. The coefficient
    below uses the actual images of the standard source frame.
    Its bound follows from 1.7.5 and 1.7.9, pp. 32–35. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorFamilyUP FamilyUpdate
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm InnerNormalization InnerNormInequalities HilbertFormCompactness
  HomInner HomSpaceTopology HomOperatorNorm ExteriorGrading ExteriorNorm FiniteExteriorPowers
  ExteriorHadamardBound ExteriorWordMultilinear
  ContinuousMultilinearUP EuclideanHomInnerCharts EuclideanStiefelInnerSplitting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Coefficient.
Variable R:realType.
Variables m n:nat.
Local Notation X:=(Hom (R_n R m) (R_n R n)).
Local Notation NX:=(inner_norm (@euclidean_hom_inner_productP R m n)).

(** Source for [euclidean_exterior_word_coefficient]: the ordered
    images g_i(e_i) give the multilinear coefficient of Q,
    supporting Federer 3.2.28(2), p. 264, through the
    exterior-power action of 1.3.2, p. 14. *)
Definition euclidean_exterior_word_coefficient (u:{ffun 'I_m->X}):
    exterior_power (R_n R n) m:=
  e_lambda (fun i=>u i (@coordinate_basis R m i)) (ord_tuple m).

(** Source for [euclidean_exterior_word_coefficient_multilinear]:
    multilinearity of the coefficient defining Q, supporting
    Federer 3.2.28(2), p. 264, by 1.4.1, p. 17. *)
Lemma euclidean_exterior_word_coefficient_multilinear:
  multilinear euclidean_exterior_word_coefficient.
Proof.
move=>u i a v w.
pose z:={ffun 'I_m->R_n R n}.
pose t:z:=[ffun j=>u j (@coordinate_basis R m j)].
have he (h:X):
  (fun j=>family_with (i:=i) u h j (@coordinate_basis R m j))=
    (fun j=>family_with (i:=i) t (h (@coordinate_basis R m i)) j).
  apply:funext=>j; case:(eqVneq i j)=>[<-|hij].
  - by rewrite !family_with_in.
  - by rewrite !family_with_out // /t ffunE.
rewrite /euclidean_exterior_word_coefficient.
rewrite !he hom_addE hom_scaleE.
exact:(@exterior_ordered_word_multilinear R (R_n R n) m t i a
  (v (@coordinate_basis R m i)) (w (@coordinate_basis R m i))).
Qed.

(** Source for [euclidean_hom_frame_evaluation_bound]: the length
    of each frame image is at most the Hilbert norm of g,
    1.7.9, p. 35. Supporting continuity bound for the
    exterior polynomial of Federer 3.2.28(2), p. 264. *)
Lemma euclidean_hom_frame_evaluation_bound (g:X) i:
  inner_norm (@euclidean_inner_productP R n) (g (@coordinate_basis R m i))<=NX g.
Proof.
have hb:=@hom_operator_norm_bound R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m) g (@coordinate_basis R m i).
have hn:inner_norm (@euclidean_inner_productP R m) (@coordinate_basis R m i)= 1.
  exact:(@orthonormal_norm1 R (R_n R m) (@euclidean_inner_product R m)
    (@euclidean_inner_productP R m) (Finite.clone 'I_m _) (@coordinate_basis R m)
    (@euclidean_coordinate_orthonormal_family R m) i).
rewrite hn mulr1 in hb.
apply:le_trans hb _.
have hNe:hom_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    (@coordinate_basisP R m) g=NX g.
  apply:inner_norm_value; first exact:inner_norm_nonnegative.
  by rewrite !inner_norm_sqr.
rewrite -hNe.
exact:(@hom_operator_norm_comparison R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m) g).1.
Qed.

(** Source for [euclidean_exterior_word_coefficient_bounded]:
    the product bound of 1.7.5, p. 32, and the frame
    evaluation bound of 1.7.9, p. 35, prove continuity of
    the actual polynomial coefficient in Federer 3.2.28(2),
    p. 264. The constant is one, also in degree zero. *)
Theorem euclidean_exterior_word_coefficient_bounded
    (h2:(1+1:R)!=0):
  norm_bounded_multilinear NX
    (@exterior_norm R h2 (R_n R n) (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) m)
    euclidean_exterior_word_coefficient.
Proof.
split; first exact:euclidean_exterior_word_coefficient_multilinear.
exists 1; split; first exact:ler01.
move=>u; rewrite mul1r.
apply:le_trans (@exterior_product_norm_bound R h2 (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m
  (fun i=>u i (@coordinate_basis R m i))) _.
apply:ler_prod=>i _; apply/andP; split; first exact:inner_norm_nonnegative.
exact:euclidean_hom_frame_evaluation_bound.
Qed.
End Coefficient.
