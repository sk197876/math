(** Federer (1969), 3.2.23, p. 260, displayed product Jacobian:
    exterior products in the two orthogonal coordinate blocks have
    multiplicative norms. All norms and exterior maps are the existing
    abstract interfaces of 1.7.5–1.7.6, pp. 32–34. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  EuclideanBlockCoordinates EuclideanBlockLinear EuclideanBlockLinearMaps
  InnerProductUP OrthogonalMaps InnerNorm ExteriorNorm ExteriorNormNaturality
  ExteriorGrading ExteriorMaps FiniteExteriorPowers ExteriorOperatorEstimate
  ExteriorHomogeneousProducts ConcatenatedFamilies ConcatenatedProducts OrthogonalWordsWedgeNorm Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_first_injection_orthogonal]: supporting
    isometry of the first coordinate inclusion for the product
    Jacobian calculation in Federer 3.2.23, p. 260. *)
Lemma euclidean_first_injection_orthogonal (R:realType) n v:
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R (n+v))
    (hom_as_linear (@euclidean_first_injection_map R n v)).
Proof.
move=>x y; rewrite /euclidean_first_injection_map /euclidean_first_injection /= euclidean_block_join_inner /=.
by rewrite (bil0l (inner_bilinear (@euclidean_inner_productP R v))) addr0.
Qed.

(** Source for [euclidean_last_injection_orthogonal]: supporting
    isometry of the second coordinate inclusion for the product
    Jacobian calculation in Federer 3.2.23, p. 260. *)
Lemma euclidean_last_injection_orthogonal (R:realType) n v:
  is_orthogonal_map (@euclidean_inner_product R v) (@euclidean_inner_product R (n+v))
    (hom_as_linear (@euclidean_last_injection_map R n v)).
Proof.
move=>x y; rewrite /euclidean_last_injection_map /euclidean_last_injection /= euclidean_block_join_inner /=.
by rewrite (bil0l (inner_bilinear (@euclidean_inner_productP R n))) add0r.
Qed.

(** Source for [euclidean_separated_exterior_norm]: the linear
    algebra behind the product Jacobian identity in Federer 3.2.23,
    p. 260. Concatenating arbitrary differential-vector families in
    separate blocks multiplies their exterior norms, including zero
    factors, deficient ranks and all zero-dimensional boundaries. *)
Theorem euclidean_separated_exterior_norm (R:realType) n v m mu
    (a:'I_m->R_n R n) (b:'I_mu->R_n R v):
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R (n+v))
    (e_lambda (concatenate_family
      (fun i=>@euclidean_first_injection R n v (a i))
      (fun j=>@euclidean_last_injection R n v (b j))) (ord_tuple (m+mu)))=
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (e_lambda a (ord_tuple m))*
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R v)
    (e_lambda b (ord_tuple mu)).
Proof.
rewrite -concatenated_product.
have hCross i j:euclidean_inner_product (@euclidean_first_injection R n v (a i))
    (@euclidean_last_injection R n v (b j))=0.
  rewrite /euclidean_first_injection /euclidean_last_injection euclidean_block_join_inner /=.
  by rewrite (bil0r (inner_bilinear (@euclidean_inner_productP R n)))
    (bil0l (inner_bilinear (@euclidean_inner_productP R v))) add0r.
rewrite (orthogonal_words_wedge_norm (euclidean_two_nonzero R)
  (@euclidean_inner_productP R (n+v)) hCross).
have hFirst:=@exterior_norm_orthogonal_natural R (euclidean_two_nonzero R)
  (R_n R n) (R_n R (n+v)) (@euclidean_inner_product R n) (@euclidean_inner_product R (n+v))
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R (n+v))
  (hom_as_linear (@euclidean_first_injection_map R n v))
  (@euclidean_first_injection_orthogonal R n v) m (e_lambda a (ord_tuple m)).
have hLast:=@exterior_norm_orthogonal_natural R (euclidean_two_nonzero R)
  (R_n R v) (R_n R (n+v)) (@euclidean_inner_product R v) (@euclidean_inner_product R (n+v))
  (@euclidean_inner_productP R v) (@euclidean_inner_productP R (n+v))
  (hom_as_linear (@euclidean_last_injection_map R n v))
  (@euclidean_last_injection_orthogonal R n v) mu (e_lambda b (ord_tuple mu)).
rewrite exterior_map_indexed_product in hFirst.
rewrite exterior_map_indexed_product in hLast.
by rewrite hFirst hLast.
Qed.
