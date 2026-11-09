(** Federer (1969), 3.4.4, p. 318: the
    actual differential of the original coordinatewise example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP EuclideanOneCoordinate
  EuclideanScalarCoordinateMaps CriticalSharpProductUP CriticalPrefixRank
  NormOpenDomainLaws NormDifferentialUP NormDifferentialLinear NormDifferentialLocal
  NormDifferentialChain NormDifferentialFiniteCalculus NormDifferentialDirectional NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_sharp_product_actual_differential]:
    Df has identity entries in the first nu coordinates
    and zero entries in the remaining coordinates on the
    original B, 3.4.4, p. 318. Actual
    scalar differentials and uniqueness identify every coordinate
    of the full differential. No rank conclusion is assumed. *)
Theorem critical_sharp_product_actual_differential (R:realType) m nu g
    (F:R_n R m->R_n R m) (x:R_n R m):
  is_critical_sharp_product_map nu g F ->
  norm_class_one (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m)) (fun _=>True) F ->
  (forall i:'I_m,(nu<=i)%N ->has_norm_differential
    (inner_norm (@euclidean_inner_productP R 1)) (fun t:R^o=>`|t|)
    (fun _=>True) g (euclidean_one_embed (x i)) 0) ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m)) (fun _=>True) F x
    (@critical_prefix_linear_map R m nu).
Proof.
move=>hF [D hD] hFlat.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hLine:=inner_norm_real_norm (@euclidean_inner_productP R 1).
pose NS:=fun t:R^o=>`|t|.
pose hNS:=@scalar_absolute_value_norm R.
have hActual:=@norm_class_one_differential R X X NX NX (fun _=>True) F D hD x Logic.I.
have hCoordinate (i:'I_m):hom_comp (euclidean_scalar_coordinate_map i) (D x)=
    if (i<nu)%N then euclidean_scalar_coordinate_map i else 0.
  have hGiven:=@norm_differential_postcompose R X X R^o NX NX NS hNX
    (fun _=>True) F x (D x) (euclidean_scalar_coordinate_map i) hActual
    (euclidean_scalar_coordinate_bounded i).
  case hIndex:(i<nu)%N.
  - have hLinear:=@norm_differential_linear R X R^o NX NS hNX hNS
      (fun _=>True) x (euclidean_scalar_coordinate_map i)
      (norm_full_domain_interior NX x) (euclidean_scalar_coordinate_bounded i).
    have hEqual:forall z:X,True ->euclidean_scalar_coordinate_map i z=
        euclidean_scalar_coordinate_map i (F z).
      move=>z _;change (z i=F z i);by rewrite hF hIndex.
    have hSecond:=norm_differential_domain_agreement hNX hEqual hLinear.
    exact:(@norm_differential_unique R X R^o NX NS hNX hNS (fun _=>True)
      (fun z=>euclidean_scalar_coordinate_map i (F z)) x
      (hom_comp (euclidean_scalar_coordinate_map i) (D x)) (euclidean_scalar_coordinate_map i) hGiven hSecond).
  - have hIndexAfter:(nu<=i)%N by rewrite leqNgt hIndex.
    have hLinear:=@norm_differential_linear R X (R_n R 1) NX
      (inner_norm (@euclidean_inner_productP R 1)) hNX hLine
      (fun _=>True) x (euclidean_one_coordinate_map i)
      (norm_full_domain_interior NX x) (euclidean_one_coordinate_bounded i).
    have hComposite:=norm_differential_chain hNX hLine hNS hLinear (hFlat i hIndexAfter).
    have hZero:hom_comp (0:Hom (R_n R 1) R^o) (euclidean_one_coordinate_map i)=0.
      by apply:hom_ext=>v;rewrite hom_compE !hom_zeroE.
    rewrite hZero in hComposite.
    have hWhole:=@norm_differential_restrict R X R^o NX NS
      (fun _=>True /\ True) (fun _=>True)
      (fun z=>g (euclidean_one_coordinate_map i z)) x 0
      (fun _ _=>conj Logic.I Logic.I) (norm_full_domain_interior NX x) hComposite.
    have hEqual:forall z:X,True ->g (euclidean_one_coordinate_map i z)=
        euclidean_scalar_coordinate_map i (F z).
      move=>z _;change (g (euclidean_one_embed (z i))=F z i);by rewrite hF hIndex.
    have hSecond:=norm_differential_domain_agreement hNX hEqual hWhole.
    exact:(@norm_differential_unique R X R^o NX NS hNX hNS (fun _=>True)
      (fun z=>euclidean_scalar_coordinate_map i (F z)) x
      (hom_comp (euclidean_scalar_coordinate_map i) (D x)) 0 hGiven hSecond).
have hEqual:D x=@critical_prefix_linear_map R m nu.
  apply:hom_ext=>v;apply/ffunP=>i.
  have h:=congr1 (fun L:Hom X R^o=>L v) (hCoordinate i).
  change ((D x v) i=(if (i<nu)%N then euclidean_scalar_coordinate_map i else 0) v) in h.
  rewrite /critical_prefix_linear_map /= ffunE.
  case hIndex:(i<nu)%N;by rewrite hIndex /= ?hom_zeroE in h.
by rewrite -hEqual.
Qed.
