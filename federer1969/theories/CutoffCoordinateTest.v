(** Federer (1969), 4.1.8, p. 360: localised
    coordinate products are actual tests in each original
    open factor. This supporting existence proof uses the
    pure products of 4.1.3, p. 348, and the
    original compact-test image laws of 4.1.1, p. 344. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormRegularityBilinear NormRegularityOperations
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothCompactSet SmoothTestSpaces SmoothTestEvaluation
  SmoothTestRepresentation CompactSupportFunctionUP TestCoordinateProductSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CutoffCoordinateTest.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable A:lmodType R.
Variable av:A->R^o->R^o.
Hypothesis hA:is_smooth_function_space hR hR (fun _=>True) av.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior N U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY U ev.
Variable u:X->R.
Hypothesis hu:norm_class_all_orders hN hR (fun _=>True) u.
Variable K:smooth_compact_set hN U.
Hypothesis hK:@real_function_support R (NormMetric.real_norm_metric_space hN) u
  `<=` smooth_compact_carrier K.

(** Source for [cutoff_coordinate_test_exists]: multiplying
    a pure coordinate scalar product and any constant target
    vector by the original compact smooth cutoff gives an
    actual test on U, supporting Federer 4.1.8, p. 360.
    No Banach or separability hypothesis is needed here. *)
Theorem cutoff_coordinate_test_exists (f:'I_n->smooth_test_space hA) (y:Y):
  exists g:smooth_test_space hE,forall x,U x->smooth_test_value hE g x=
    (u x*(\prod_i smooth_test_value hA (f i) (x i)))*:y.
Proof.
pose v:=fun x:X=>(u x*(\prod_i smooth_test_value hA (f i) (x i)))*:y.
have hClass:norm_class_all_orders hN hNY U v.
  move=>k.
  have hScalar:=norm_class_scalar_product (hu k)
    (@test_coordinate_product_smooth R n A av hA f k).
  have hLocal:=@norm_class_open_restriction R X R^o N (fun t:R^o=>`|t|)
    hN hR (fun _=>True) U
    (fun x:X=>u x*(\prod_i smooth_test_value hA (f i) (x i))) k
    (fun _ _=>I) hU hScalar.
  exact:(norm_class_scalar_product hLocal (@norm_class_constant R X Y N NY hN hNY U y k hU)).
have hOff:forall x,~smooth_compact_carrier K x->v x=0.
  move=>x hx.
  have hNot:~@real_function_support R (NormMetric.real_norm_metric_space hN) u x.
    move=>h;exact (hx (@hK x h)).
  by rewrite /v (@real_function_zero_off_support R (NormMetric.real_norm_metric_space hN) u x hNot)
    mul0r scale0r.
exact:(@smooth_test_represents_compact_function R X Y N NY hN hNY U E ev hE K v hClass hOff).
Qed.
End CutoffCoordinateTest.
