(** Federer (1969), 2.10.38, printed pp. 198–199: the norm of every initial
    endpoint product factors as the first chord length times the norm of the
    projected remaining product. Prove the exact equality in every degree,
    including an empty remaining product, from the public exterior and
    orthogonality laws. Neither passage states the compact enclosing-box
    theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps CoordinateProjection OrthonormalFamilies InnerProductUP OrthogonalMaps
  NormalHeadChartGeometry EuclideanHeadExteriorBound ExteriorAlgebra ExteriorGrading
  ExteriorHomogeneousProducts FiniteExteriorPowers ExteriorMaps ExteriorOperatorEstimate
  ExteriorParallelShifts ExteriorNorm ExteriorNormNaturality AssociatedSubspace SimpleElementary
  ProductAssociatedOrthogonality SimpleWedgeEquality GradedComponents Bilinear ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [coordinate_head_tail_orthogonal]: supporting
    perpendicular head and tail subspaces in
    the projection calculation of 2.10.38,
    p. 199. This follows from the
    specified coordinate inclusion and dot product. *)
Lemma coordinate_head_tail_orthogonal (R : realType) (n : nat) (x : R_n R n) :
  euclidean_inner_product (@coordinate_basis R n.+1 ord0) (coordinate_tail_inclusion x)=0.
Proof.
rewrite euclidean_inner_symmetric euclidean_inner_basis.
by rewrite /coordinate_tail_inclusion ffunE unlift_none.
Qed.

(** Source for [coordinate_head_tail_product_norm]: supporting
    isometric factorisation in 2.10.38,
    p. 199. Wedging a tail product with
    the unit first axis preserves its norm,
    including the empty and zero tail products. *)
Theorem coordinate_head_tail_product_norm (R : realType) (n k : nat)
    (w : 'I_k -> R_n R n) :
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n.+1)
    (exterior_product
      (e_lambda (fun _ : 'I_1=>@coordinate_basis R n.+1 ord0) (ord_tuple 1))
      (e_lambda (fun i=>coordinate_tail_inclusion (w i)) (ord_tuple k)))=
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (e_lambda w (ord_tuple k)).
Proof.
pose h2 := euclidean_two_nonzero R.
pose hB := @euclidean_inner_productP R n.+1.
pose e0 := @coordinate_basis R n.+1 ord0.
pose I := GRing.Linear.clone _ _ _ _ (@coordinate_tail_inclusion R n) _.
pose X := e_lambda (fun _ : 'I_1=>e0) (ord_tuple 1).
pose Y := e_lambda (fun i : 'I_k=>I (w i)) (ord_tuple k).
have hX : exterior_norm h2 hB X= 1.
  apply: orthonormal_product_unit_norm=> i j.
  rewrite /e0 euclidean_inner_basis /coordinate_basis ffunE eqxx.
  by rewrite !ord1 eqxx.
have hXne : X!=0.
  by apply/eqP=> hz; move: hX; rewrite hz exterior_norm_zero=> /eqP; rewrite eq_sym oner_eq0.
have hprod : exterior_norm h2 hB (exterior_product X Y)=exterior_norm h2 hB Y.
  case: (eqVneq Y 0)=> [hy|hy].
  - by rewrite hy (bil0r (@exterior_product_bilinear R (R_n R n.+1) 1 k)) !exterior_norm_zero.
  - have ho : forall x y, FedererSimple.T X x -> FedererSimple.T Y y ->
        euclidean_inner_product x y=0.
      apply: (proj2 (@product_associated_orthogonality R h2 (R_n R n.+1) _ hB
        1 k (fun _=>e0) (fun i=>I (w i)) hXne hy))=> i j.
      exact: coordinate_head_tail_orthogonal.
    have hh := (proj2 (@simple_wedge_norm_equality R h2 (R_n R n.+1) _ hB
      1 k X Y hXne hy (product_simple _) (product_simple _))) ho.
    by rewrite hX mul1r in hh.
change (exterior_norm h2 hB (exterior_product X Y)=
  exterior_norm h2 (@euclidean_inner_productP R n) (e_lambda w (ord_tuple k))).
rewrite hprod /Y -exterior_map_indexed_product.
exact: (@exterior_norm_orthogonal_natural R h2 (R_n R n) (R_n R n.+1) _ _
  (@euclidean_inner_productP R n) hB I (@coordinate_tail_inclusion_orthogonal R n)).
Qed.

(** Source for [euclidean_head_exterior_product_factor]: direct
    intermediate norm equality in the computation
    of 2.10.38, p. 199, in a
    specified orthogonal head/tail chart. Every
    remaining degree is allowed, including zero
    and degrees exceeding the tail dimension. *)
Theorem euclidean_head_exterior_product_factor (R : realType) (n k : nat)
    (v : 'I_k.+1 -> R_n R n.+1) (h : R) :
  v ord0=@coordinate_head_inclusion R n h ->
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n.+1)
    (e_lambda v (ord_tuple k.+1))=
  `|h|*exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (e_lambda (fun i=>coordinate_tail (v (lift ord0 i))) (ord_tuple k)).
Proof.
move=> hv.
pose e0 := @coordinate_basis R n.+1 ord0.
pose w (i : 'I_k) := coordinate_tail (v (lift ord0 i)).
pose I := GRing.Linear.clone _ _ _ _ (@coordinate_tail_inclusion R n) _.
pose X := e_lambda (fun _ : 'I_1=>e0) (ord_tuple 1).
pose Y := e_lambda (fun i : 'I_k=>I (w i)) (ord_tuple k).
have he : e_lambda v (ord_tuple k.+1)=
    exterior_reindex (add1n k) (h*:exterior_product X Y).
  apply: val_inj.
  change (component_val (e_lambda v (ord_tuple k.+1))=
    component_val (exterior_reindex (add1n k) (h*:exterior_product X Y))).
  rewrite exterior_reindexE linearZ.
  change (component_val (e_lambda v (ord_tuple k.+1))=
    h*:component_val (exterior_product X Y)).
  rewrite exterior_productE /X /Y !e_lambdaE.
  rewrite /ord_tuple /= (@enum_ordSl 0) enum_ord0 /=.
  change (exterior_word [seq v i | i <- enum 'I_k.+1]=
    h*:wedge (exterior_word [:: e0]) (exterior_word [seq I (w i) | i <- enum 'I_k])).
  rewrite enum_ordSl map_cons -map_comp !exterior_word_cons hv coordinate_head_inclusion_axis
    linearZ (bilZl (wedge_bilinear (R_n R n.+1))) exterior_word_nil wedge_unitr.
  congr (h*:_).
  have hex (i : 'I_k) : v (lift ord0 i)=I (w i)+coordinate_head (v (lift ord0 i))*:e0.
    rewrite /I /w /e0 -coordinate_head_inclusion_axis addrC; symmetry; exact: coordinate_decomposition.
  have hm : [seq v (lift ord0 i) | i <- enum 'I_k]=
    [seq I (w i)+coordinate_head (v (lift ord0 i))*:e0 | i <- enum 'I_k].
    by apply: eq_map=> i; exact: hex.
  by rewrite hm exterior_parallel_shift_prefix.
rewrite he exterior_norm_reindex exterior_norm_scale.
congr (`|h|*_); exact: coordinate_head_tail_product_norm.
Qed.
