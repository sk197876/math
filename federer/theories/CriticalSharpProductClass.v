(** Federer (1969), 3.4.4, p. 318: existence,
    uniqueness, and class k of the actual printed product map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP EuclideanOneCoordinate
  EuclideanScalarCoordinateMaps EuclideanScalarAssemblyClass CriticalSharpProductUP
  NormDifferentialUP NormOpenDomainLaws NormRegularity NormRegularityOperations NormRegularityLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_sharp_product_map_exists]: existence
    of the exact map specified in 3.4.4, p. 318.
    The coordinate construction serves only as an existence witness. *)
Lemma critical_sharp_product_map_exists (R:realType) (m nu:nat)
    (g:inner_metric_space (@euclidean_inner_productP R 1)->R^o):
  exists F:R_n R m->R_n R m,is_critical_sharp_product_map nu g F.
Proof.
exists (fun x:R_n R m=>[ffun i:'I_m=>if (i<nu)%N then x i else g (euclidean_one_embed (x i))]).
by move=>x i;rewrite ffunE.
Qed.

(** Source for [critical_sharp_product_map_unique]: the printed
    coordinates determine the actual map uniquely, supporting
    its definition in 3.4.4, p. 318. *)
Lemma critical_sharp_product_map_unique (R:realType) m nu g
    (F G:R_n R m->R_n R m):
  is_critical_sharp_product_map nu g F ->is_critical_sharp_product_map nu g G ->F=G.
Proof.
move=>hF hG;apply:funext=>x;apply/ffunP=>i;by rewrite hF hG.
Qed.

(** Source for [critical_sharp_product_map_class]: the actual
    original map is of class k, 3.4.4, p. 318.
    Bounded source coordinates, composition with the proved
    flat extension, and finite target assembly prove this
    under the original whole-space convention. *)
Theorem critical_sharp_product_map_class (R:realType) m nu g
    (F:R_n R m->R_n R m) k:
  is_critical_sharp_product_map nu g F ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R 1))
    (@scalar_absolute_value_norm R) (fun _=>True) g k ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R m)) (fun _=>True) F k.
Proof.
move=>hF hG.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hLine:=inner_norm_real_norm (@euclidean_inner_productP R 1).
pose C (i:'I_m) (x:X):R^o:=if (i<nu)%N then x i else g (euclidean_one_embed (x i)).
have hEach i:norm_class hNX (@scalar_absolute_value_norm R) (fun _=>True) (C i) k.
  case hIndex:(i<nu)%N.
  - have hLinear:=@norm_class_linear R X R^o NX (fun t:R^o=>`|t|) hNX
      (@scalar_absolute_value_norm R) (fun _=>True) (euclidean_scalar_coordinate_map i) k
      (fun x _=>norm_full_domain_interior NX x) (euclidean_scalar_coordinate_bounded i).
    have hEqual:C i=(fun x=>euclidean_scalar_coordinate_map i x).
      by apply:funext=>x;rewrite /C hIndex.
    by rewrite hEqual.
  - have hCompose:=@norm_class_precompose_linear R X (R_n R 1) R^o NX
      (inner_norm (@euclidean_inner_productP R 1)) (fun t:R^o=>`|t|)
      hNX hLine (@scalar_absolute_value_norm R) (fun _=>True) g
      (euclidean_one_coordinate_map i) k (euclidean_one_coordinate_bounded i) hG.
    have hEqual:C i=(fun x=>g (euclidean_one_coordinate_map i x)).
      by apply:funext=>x;rewrite /C hIndex.
    by rewrite hEqual.
have hAssembly:=@euclidean_scalar_assembly_class R X NX hNX (fun _=>True) m C k
  (fun x _=>norm_full_domain_interior NX x) hEach.
apply:(@norm_class_domain_agreement R X X NX NX hNX hNX (fun _=>True)
  (fun x=>[ffun i=>C i x]) F k _ hAssembly).
move=>x _;apply/ffunP=>i;by rewrite ffunE /C hF.
Qed.
