(** Federer (1969), 3.2.47, pp. 282–283: a proved
    product diffeomorphism provides actual local coordinates on
    Phi inverse(E). The following chart lemma separates the
    general coordinate argument from the orthogonal-group algebra;
    every product, regularity and inverse law is an obligation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness ProductInner
  RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  NormCoordinateSystemUP NormCartesianRegularity InnerCartesianParameterRegularity
  EuclideanBlockCoordinates EuclideanCartesianMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Pullback.
Variable R:realType.
Variables X V W:lmodType R.
Variables (BX:X->X->R) (BV:V->V->R) (BW:W->W->R).
Hypotheses (hX:@is_inner_product R X BX)
  (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW).
Local Notation hNX:=(inner_norm_real_norm hX).
Local Notation hNV:=(inner_norm_real_norm hV).
Local Notation hNW:=(inner_norm_real_norm hW).
Local Notation hNP:=(inner_norm_real_norm (product_inner_productP hV hW)).
Local Notation P:=[the lmodType R of (V*W)%type].
Variables (S D:set X) (E:set V) (I:set W) (B:set P).
Variables (p:X->V) (h:X->W) (j:P->X).
Variables r mu k:nat.
Variables (TE:set V) (TI:set W) (QE:set (R_n R r)) (QI:set (R_n R mu)).
Variables (phiE:V->R_n R r) (psiE:R_n R r->V).
Variables (phiI:W->R_n R mu) (psiI:R_n R mu->W).
Hypothesis hCE:is_norm_coordinate_system hNV
  (inner_norm_real_norm (@euclidean_inner_productP R r)) E TE QE phiE psiE k.
Hypothesis hCI:is_norm_coordinate_system hNW
  (inner_norm_real_norm (@euclidean_inner_productP R mu)) I TI QI phiI psiI k.
Hypothesis hp:norm_class hNX hNV D p k.
Hypothesis hh:norm_class hNX hNW D h k.
Hypothesis hj:norm_class hNP hNX B j k.
Hypothesis hDomain:forall a b,E a ->I b ->B (a,b).
Hypothesis hForward:forall x,S x ->D x ->
  E (p x) /\ I (h x) /\ j (p x,h x)=x.
Hypothesis hBackward:forall a b,E a ->I b ->
  S (j (a,b)) /\p (j (a,b))=a /\D (j (a,b)) /\h (j (a,b))=b.

(** Source for [product_chart_pullback_coordinates]: the local
    coordinate consequence of the printed product diffeomorphism,
    3.2.47, pp. 282–283. The exact image is
    the original source intersected with the actual open chart
    domain; no replacement source or tangent is assumed. *)
Theorem product_chart_pullback_coordinates:
  let A:=fun x=> (D x /\TE (p x)) /\(D x /\TI (h x)) in
  let Q:=euclidean_cartesian_set QE QI in
  let phi:=fun x=>euclidean_block_join (phiE (p x),phiI (h x)) in
  let psi:=fun z=>j (psiE (euclidean_block_split z).1,psiI (euclidean_block_split z).2) in
  is_norm_coordinate_system hNX
    (inner_norm_real_norm (@euclidean_inner_productP R (r+mu))) S A Q phi psi k.
Proof.
move=>A Q phi psi.
pose hNR:=inner_norm_real_norm (@euclidean_inner_productP R r).
pose hNM:=inner_norm_real_norm (@euclidean_inner_productP R mu).
pose hNQ:=inner_norm_real_norm (@euclidean_inner_productP R (r+mu)).
have hLeft:=@norm_class_composition R X V (R_n R r) _ _ _ hNX hNV hNR
  D TE p phiE k hp (norm_coordinate_class_forward hCE).
have hRight:=@norm_class_composition R X W (R_n R mu) _ _ _ hNX hNW hNM
  D TI h phiI k hh (norm_coordinate_class_forward hCI).
have hOpen x (hx:A x):norm_domain_interior (inner_norm hX) A x.
  exact (@norm_intersection_domain_interior R X _ _ _ x
    ((@norm_class_continuous R X (R_n R r) _ _ hNX hNR _ _ k hLeft x hx.1).1)
    ((@norm_class_continuous R X (R_n R mu) _ _ hNX hNM _ _ k hRight x hx.2).1)).
have hLeftA:=@norm_class_open_restriction R X (R_n R r) _ _ hNX hNR
  _ A (fun x=>phiE (p x)) k (fun x hx=>hx.1) hOpen hLeft.
have hRightA:=@norm_class_open_restriction R X (R_n R mu) _ _ hNX hNM
  _ A (fun x=>phiI (h x)) k (fun x hx=>hx.2) hOpen hRight.
have hPhi:=@norm_class_euclidean_block_pair R X _ hNX r mu A
  (fun x=>phiE (p x)) (fun x=>phiI (h x)) k hLeftA hRightA.
have hPair:=@inner_cartesian_parameter_norm_class R V W BV BW hV hW r mu
  QE QI psiE psiI k (norm_coordinate_class_backward hCE) (norm_coordinate_class_backward hCI).
have hMap z (hz:Q z):B (psiE (euclidean_block_split z).1,psiI (euclidean_block_split z).2).
  exact (@hDomain _ _ (norm_coordinate_backward_membership hCE hz.1).1
    (norm_coordinate_backward_membership hCI hz.2).1).
have hPsi:=@norm_class_compose_on R (R_n R (r+mu)) P X _ _ _ hNQ hNP hNX
  Q B (fun z=>(psiE (euclidean_block_split z).1,psiI (euclidean_block_split z).2)) j k
  hMap hPair hj.
constructor.
- exact hPhi.
- exact hPsi.
- move=>x hx.
  change (QE (euclidean_block_split (euclidean_block_join (phiE (p x),phiI (h x)))).1 /\
    QI (euclidean_block_split (euclidean_block_join (phiE (p x),phiI (h x)))).2).
  rewrite euclidean_block_joinK; split.
  + exact (norm_coordinate_forward_range hCE hx.1.2).
  + exact (norm_coordinate_forward_range hCI hx.2.2).
- apply/seteqP; split=>x.
  + move=>[z hz <-].
    have hE:=norm_coordinate_backward_membership hCE hz.1.
    have hI:=norm_coordinate_backward_membership hCI hz.2.
    have [hS [hP [hD hH]]]:=@hBackward _ _ hE.1 hI.1.
    split; first exact hS.
    split; split; try exact hD.
    * change (TE (p (j (psiE (euclidean_block_split z).1,psiI (euclidean_block_split z).2)))).
      rewrite hP; exact hE.2.
    * change (TI (h (j (psiE (euclidean_block_split z).1,psiI (euclidean_block_split z).2)))).
      rewrite hH; exact hI.2.
  + move=>[hx hxA].
    have [hE [hI hJ]]:=@hForward x hx hxA.1.1.
    exists (phi x).
    * change (QE (euclidean_block_split (euclidean_block_join (phiE (p x),phiI (h x)))).1 /\
        QI (euclidean_block_split (euclidean_block_join (phiE (p x),phiI (h x)))).2).
      rewrite euclidean_block_joinK; split.
      -- exact (norm_coordinate_forward_range hCE hxA.1.2).
      -- exact (norm_coordinate_forward_range hCI hxA.2.2).
    * change (j (psiE (euclidean_block_split (euclidean_block_join (phiE (p x),phiI (h x)))).1,
        psiI (euclidean_block_split (euclidean_block_join (phiE (p x),phiI (h x)))).2)=x).
      rewrite euclidean_block_joinK /= (norm_coordinate_base_inverse hCE hE hxA.1.2)
        (norm_coordinate_base_inverse hCI hI hxA.2.2); exact hJ.
- move=>z hz.
  have hE:=norm_coordinate_backward_membership hCE hz.1.
  have hI:=norm_coordinate_backward_membership hCI hz.2.
  have [_ [hP [_ hH]]]:=@hBackward _ _ hE.1 hI.1.
  change (euclidean_block_join
    (phiE (p (j (psiE (euclidean_block_split z).1,psiI (euclidean_block_split z).2))),
     phiI (h (j (psiE (euclidean_block_split z).1,psiI (euclidean_block_split z).2))))=z).
  rewrite hP hH (norm_coordinate_cancel hCE hz.1) (norm_coordinate_cancel hCI hz.2).
  exact:euclidean_block_splitK.
Qed.
End Pullback.
