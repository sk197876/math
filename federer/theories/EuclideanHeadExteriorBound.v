(** Federer (1969), 2.10.36, printed p. 198: split off the first chord and
    project the other factors to its perpendicular hyperplane. Parallel
    shifts disappear by the exterior laws of 1.3.1, p. 13. The simple-factor
    norm inequality of 1.7.5, p. 32, then supplies the required product
    bound. This upper bound suffices in place of the printed equality of
    norms. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  CoordinateProjection OrthogonalMaps InnerProductUP InnerNorm InnerMetric OrthonormalFamilies
  EuclideanCoordinateSplit EuclideanNormalChartUP NormalHeadChartGeometry
  ExteriorAlgebra ExteriorGrading ExteriorHomogeneousProducts FiniteExteriorPowers
  ExteriorMaps ExteriorMapScaling ExteriorParallelShifts ExteriorNorm ExteriorOperatorEstimate ExteriorNormNaturality
  SimpleWedgeNorm SimpleElementary AssociatedSubspace GradedComponents Bilinear TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [coordinate_tail_inclusion_orthogonal]: supporting
    isometric identification of the projected hyperplane
    in 2.10.36, p. 198. The defining
    coordinate inclusion preserves the dot product,
    including an empty tail. *)
Lemma coordinate_tail_inclusion_orthogonal (R : realType) (n : nat) :
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n.+1)
    (GRing.Linear.clone _ _ _ _ (@coordinate_tail_inclusion R n) _).
Proof.
move=> x y; rewrite /euclidean_inner_product big_ord_recl.
rewrite /coordinate_tail_inclusion !ffunE unlift_none mul0r add0r.
apply: eq_bigr=> i _.
by rewrite !ffunE liftK.
Qed.

(** Source for [euclidean_head_exterior_product_bound]: supporting
    first exterior-product comparison in 2.10.36,
    p. 198. If the first factor is
    h times the first coordinate vector, its
    norm is bounded by |h| times the
    norm of the exterior product of the tails
    of the remaining factors. *)
Theorem euclidean_head_exterior_product_bound (R : realType) (n : nat)
    (v : 'I_n.+1 -> R_n R n.+1) (h : R) :
  v ord0=@coordinate_head_inclusion R n h ->
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n.+1)
    (e_lambda v (ord_tuple n.+1)) <=
  `|h|*exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (e_lambda (fun i => coordinate_tail (v (lift ord0 i))) (ord_tuple n)).
Proof.
move=> hv.
pose h2 := euclidean_two_nonzero R.
pose hB := @euclidean_inner_productP R n.+1.
pose e0 := @coordinate_basis R n.+1 ord0.
pose w (i : 'I_n) := coordinate_tail (v (lift ord0 i)).
pose I := GRing.Linear.clone _ _ _ _ (@coordinate_tail_inclusion R n) _.
pose X := e_lambda (fun _ : 'I_1 => e0) (ord_tuple 1).
pose Y := e_lambda (fun i : 'I_n => I (w i)) (ord_tuple n).
have he : e_lambda v (ord_tuple n.+1)=
    exterior_reindex (add1n n) (h*:exterior_product X Y).
  apply: val_inj.
  change (component_val (e_lambda v (ord_tuple n.+1))=
    component_val (exterior_reindex (add1n n) (h*:exterior_product X Y))).
  rewrite exterior_reindexE linearZ.
  change (component_val (e_lambda v (ord_tuple n.+1))=
    h*:component_val (exterior_product X Y)).
  rewrite exterior_productE /X /Y !e_lambdaE.
  rewrite /ord_tuple /= (@enum_ordSl 0) enum_ord0 /=.
  change (exterior_word [seq v i | i <- enum 'I_n.+1]=
    h*:wedge (exterior_word [:: e0]) (exterior_word [seq I (w i) | i <- enum 'I_n])).
  rewrite enum_ordSl map_cons -map_comp !exterior_word_cons hv coordinate_head_inclusion_axis
    linearZ (bilZl (wedge_bilinear (R_n R n.+1))).
  rewrite exterior_word_nil wedge_unitr.
  congr (h*:_).
  have hex (i : 'I_n) : v (lift ord0 i)=I (w i)+coordinate_head (v (lift ord0 i))*:e0.
    rewrite /I /w /e0 -coordinate_head_inclusion_axis addrC; symmetry; exact: coordinate_decomposition.
  have hm : [seq v (lift ord0 i) | i <- enum 'I_n]=
    [seq I (w i)+coordinate_head (v (lift ord0 i))*:e0 | i <- enum 'I_n].
    by apply: eq_map=> i; exact: hex.
  by rewrite hm exterior_parallel_shift_prefix.
have hX : exterior_norm h2 hB X= 1.
  apply: orthonormal_product_unit_norm=> i j.
  rewrite /e0 euclidean_inner_basis /coordinate_basis ffunE eqxx.
  by rewrite !ord1 eqxx.
have hsimple : simple X := product_simple _.
have hineq := simple_wedge_norm_bound h2 hB (or_introl hsimple : simple X \/ simple Y).
rewrite he exterior_norm_reindex exterior_norm_scale.
apply: le_trans (ler_wpM2l (normr_ge0 h) hineq) _.
rewrite hX mul1r /Y -exterior_map_indexed_product
  (@exterior_norm_orthogonal_natural R h2 (R_n R n) (R_n R n.+1) _ _
    (@euclidean_inner_productP R n) hB I (@coordinate_tail_inclusion_orthogonal R n)).
exact: lexx.
Qed.
