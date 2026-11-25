(** Federer (1969), 4.1.3, p. 348: the coordinate product
    of one-variable tests, multiplied by an actual vector,
    belongs to D(R^n,Y). Smoothness and compact support
    precede realization in the abstract test space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormRegularity NormRegularityOperations NormRegularityBilinear GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness FiniteNormEquivalence
  SmoothCompactSet SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothTestRepresentation
  TestCoordinateProductSmooth TestCoordinateProductSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestCoordinateProductRepresentation.
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
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.

(** Source for [test_coordinate_vector_product_exists]: the pure
    coordinate tensor has its actual compactly supported smooth
    value, Federer 4.1.3, p. 348. No completeness or separability
    of Y is needed for this algebraic map. *)
Theorem test_coordinate_vector_product_exists (f:'I_n->smooth_test_space hA) (y:Y):
  exists g:smooth_test_space hE,forall x:X,
    smooth_test_value hE g x=(\prod_i smooth_test_value hA (f i) (x i))*:y.
Proof.
have[b [hb hOff]]:=@test_coordinate_product_support_bound R n A av hA f.
have hCompact:compact [set x:real_norm_metric_space hN|N x<=b].
  have hc:=@finite_norm_closed_ball_compact R X n (@coordinate_basis R n)
    (@coordinate_basisP R n) N hN 0 b.
  have hEq:[set x:real_norm_metric_space hN|N (x-0)<=b]=[set x:real_norm_metric_space hN|N x<=b].
    apply:funext=>x.
    change (is_true (N (x-0)<=b)=is_true (N x<=b)).
    by rewrite subr0.
  by rewrite hEq in hc.
pose K:=@Build_smooth_compact_set R X N hN (fun _=>True)
  [set x|N x<=b] (fun _ _=>I) hCompact.
have hClass:norm_class_all_orders hN hNY (fun _=>True)
    (fun x:X=>(\prod_i smooth_test_value hA (f i) (x i))*:y).
  move=>k.
  have hC:=@norm_class_constant R X Y N NY hN hNY (fun _=>True) y k
    (fun x _=>norm_full_domain_interior N x).
  exact:(norm_class_scalar_product (@test_coordinate_product_smooth R n A av hA f k) hC).
have hZero x:~smooth_compact_carrier K x ->
    (\prod_i smooth_test_value hA (f i) (x i))*:y=0.
  move=>hx; have hLarge:b<N x by rewrite ltNge; apply/negP=>h; exact:hx h.
  by rewrite (hOff x hLarge) scale0r.
have[g hg]:=@smooth_test_represents_compact_function R X Y N NY hN hNY
  (fun _=>True) E ev hE K _ hClass hZero.
exists g=>x; exact:(hg x I).
Qed.
End TestCoordinateProductRepresentation.
