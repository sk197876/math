(** Federer (1969), 3.1.20, p. 233: continuity needed for the
    maximal-rank argument. This supporting trace route expands the
    finite coordinate formula of 1.4.5 rather than importing an
    external matrix or manifold calculus. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import Hom TensorUP Bilinear RealNormUP LinearBasis FiniteCoordinates FiniteDualDimension
  Annihilator GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanCoordinateTopology EuclideanCoordinateMetric TraceDefinition NormDifferentialUP NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_coordinate_dual_basis]: supporting the
    coordinate trace formula in the converse of 3.1.20, p. 233,
    from the basis expansion of 1.6.3, p. 25. The standard dual
    basis evaluates the corresponding coordinate. *)
Lemma euclidean_coordinate_dual_basis (K:realFieldType) n i (x:R_n K n) :
  dual_basis (@coordinate_basisP K n) i x=x i.
Proof.
have hev:linear (fun y:R_n K n=>y i).
  move=>c z w; by rewrite !ffunE.
pose ev:=@HomMap K (R_n K n) K^o (fun y=>y i) (introT (asboolP _) hev).
apply: (@basis_linear_ext K (Choice.clone 'I_n _) (R_n K n) (@coordinate_basis K n)
  (@coordinate_basisP K n) K^o
  (hom_as_linear (dual_basis (@coordinate_basisP K n) i)) (hom_as_linear ev) _ x).
move=>j; change (dual_basis (@coordinate_basisP K n) i (@coordinate_basis K n j)=(@coordinate_basis K n j) i).
by rewrite dual_basisE /coordinate_basis ffunE eq_sym.
Qed.

(** Source for [euclidean_trace_field_continuous]: the trace of
    a continuous differential field is continuous on its open
    domain, supporting the maximal-rank separation in Federer
    3.1.20, p. 233. The bound uses the finite sum of coordinate
    evaluations; zero ambient dimension is included. *)
Lemma euclidean_trace_field_continuous (R:realType) (h2:(1+1:R)!=0) n
    (A:R_n R n->Prop) (f:R_n R n->R_n R n) (D:R_n R n->Hom (R_n R n) (R_n R n)) :
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R n)) A f D ->
  norm_class_zero (inner_norm (@euclidean_inner_productP R n)) (fun t:R^o=>`|t|) A
    (fun x=>@trace_Hom R h2 (R_n R n) (Finite.clone 'I_n _)
      (@coordinate_basis R n) (@coordinate_basisP R n) (D x)).
Proof.
move=>hD a ha; split; first exact (norm_class_one_zero hD ha).1.
move=>e he.
pose delta:=e/(n%:R+1).
have hn:0<(n%:R+1:R).
  have hnn:(0:R)<=n%:R by rewrite ler0n.
  by lra.
have hd:0<delta by rewrite /delta divr_gt0.
have [r [hr hbound]]:=norm_class_one_continuity hD ha hd.
exists r; split=>// h hah hhr.
rewrite -linearB trace_HomE.
change (is_true (`|\sum_i (dual_basis (@coordinate_basisP R n) i
  ((D (a+h)-D a) (@coordinate_basis R n i)):R)|<e)).
have htriangle:=@real_seminorm_sum R R^o (fun t:R^o=>`|t|)
  (scalar_absolute_value_norm R).1 (Finite.clone 'I_n _)
  (fun i=>dual_basis (@coordinate_basisP R n) i
    ((D (a+h)-D a) (@coordinate_basis R n i))).
apply: le_lt_trans htriangle _.
have hsum:(\sum_i `|dual_basis (@coordinate_basisP R n) i ((D (a+h)-D a) (@coordinate_basis R n i))|)<=n%:R*delta.
  have hh:(\sum_i `|dual_basis (@coordinate_basisP R n) i ((D (a+h)-D a) (@coordinate_basis R n i))|)<=
      \sum_(i:'I_n) delta.
    apply: ler_sum=>i _; rewrite euclidean_coordinate_dual_basis.
    apply: le_trans (euclidean_coordinate_norm_bound i _) _.
    have hb:=hbound h hah hhr (@coordinate_basis R n i).
    by rewrite euclidean_coordinate_unit_norm mulr1 in hb.
  by rewrite sumr_const card_ord -mulr_natl in hh.
apply: le_lt_trans hsum _.
have hcancel:delta*(n%:R+1)=e by rewrite /delta divfK // gt_eqF.
by nra.
Qed.
