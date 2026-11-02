(** Federer (1969), 3.1.14, p. 226:
    on U the differentials of the extension g and of any
    polynomial Q are finite sums over the overlap set S_x of
    3.1.13, so that D^i g(x)-D^i Q(x) is the sum over S_x of
    the differentials of v_s (P_{xi(s)}-Q). *)
From mathcomp Require Import all_boot all_order all_algebra boolp finmap classical_sets
  cardinality reals topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness RealNormUP
  BoundedHom PolynomialFunctions PolynomialRepresentations
  ContinuousMultilinearUP NormDifferentialUP NormClassHigherUP NormClassHigherFields
  NormClassHigherArithmetic NormHigherDifferentialArithmetic NormHigherDifferentialUnique
  NormBoundedBilinearUP NormClassHigherBilinear NormHigherDifferentialUP
  InnerNearestUP FiniteInnerPolynomialSmoothness
  FiniteFamilySumUP NormLocallyFiniteFamilyUP NormLocalFiniteSumDifferentials
  NormPartitionUnityUP CompactSupportFunctionUP MetricClosedBalls
  FedererCoverRadius LipschitzRadiusOverlap EuclideanPartitionBallCoverUP
  EuclideanPartitionFamilyUP EuclideanPartitionOverlapNeighborhood
  WhitneyExtensionFunction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section WhitneyDerivativeSums.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Y : lmodType R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N NY (@ev i) (@ZN i).
Variable W : nat->lmodType R.
Variable ew : forall i, {ffun 'I_i->R_n R m}->Hom (W i) R^o.
Variable WN : forall i, W i->R.
Hypothesis hW : forall i, is_continuous_multilinear_space N (fun t : R^o=>`|t|) (@ew i) (@WN i).
Variable A : set X.
Hypothesis hA : closed A.
Variable P : X->PolynomialFunction (R_n R m) Y.
Variable xi : X->X.
Local Notation Phi := ([set (~` A : set X)]).
Local Notation U := (\bigcup_(T in Phi) T).
Local Notation h := (federer_cover_radius Phi).
Variable S : set X.
Variables (sigma : X->R) (v : X->X->R).
Hypothesis hS : is_federer_partition_ball_cover Phi S.
Hypothesis hfamily : is_euclidean_partition_family ew WN Phi S sigma v.
Local Notation g := (whitney_extension P xi hfamily).
Local Notation Sx := (fun x=>lipschitz_radius_overlap S h 10 10 x).
Local Notation O := (partition_overlap_neighborhood Phi).

(** Source for [whitney_overlap_fset]:
    the finite overlap set S_x of 3.1.13 as a finite set
    of centres, Federer 3.1.14, p. 226. *)
Definition whitney_overlap_fset (x : X) : {fset X} := fset_set (Sx x).

(** Source for [whitney_overlap_fset_member]:
    members of the finite overlap set are selected centres,
    Federer 3.1.14, p. 226. *)
Lemma whitney_overlap_fset_member x : U x ->
  forall s, s \in whitney_overlap_fset x -> S s.
Proof.
move=>hx s; rewrite /whitney_overlap_fset in_fset_set; last exact: (partition_ball_overlap_finite hS hx).
by move/set_mem=>[hs _].
Qed.

(** Source for [whitney_partition_vanishes_off_overlap]:
    "s in S_x" is required for v_s(y) to be nonzero near
    x, Federer 3.1.14, p. 226, by the support law
    spt v_s in B[s,10h(s)] of 3.1.13 and the overlap
    neighbourhood law. *)
Lemma whitney_partition_vanishes_off_overlap x : U x ->
  forall y, O x y -> forall s, S s -> s \notin whitney_overlap_fset x -> v s y=0.
Proof.
move=>hx y hy s hs hn; apply: contrapT=>hne.
have ho := whitney_family_open hA.
have [_ [_ [_ hmeet]]] := partition_overlap_neighborhood_laws S ho hx.
have hsupp : real_function_support (v s) y.
  by apply: subset_closure; exact hne.
have hball := partition_family_support_ball hfamily hs hsupp.
have hin : s \in whitney_overlap_fset x.
  rewrite /whitney_overlap_fset in_fset_set; last exact: (partition_ball_overlap_finite hS hx).
  apply/mem_set; exact: (hmeet s y hs hy hball).
by move: hn; rewrite hin.
Qed.

(** Source for [whitney_difference_summand]:
    the summand v_s (P_{xi(s)}-Q), Federer 3.1.14, p. 226,
    in the expression of D^i g(x)-D^i Q(x). *)
Definition whitney_difference_summand (Q : PolynomialFunction (R_n R m) Y) (s y : X) : Y :=
  v s y*:((P (xi s)) y-Q y).

(** Source for [whitney_polynomial_difference_class]:
    the difference of two polynomials is of class infinity
    on R^m, Federer 3.1.14, p. 226. *)
Lemma whitney_polynomial_difference_class (P' Q : PolynomialFunction (R_n R m) Y) (B : set X) :
  (forall x, B x -> norm_domain_interior N B x) ->
  norm_class_infinity N NY ev ZN B (fun y : X=>P' y-Q y).
Proof.
move=>hB k.
have hP := @finite_inner_polynomial_smooth R (R_n R m) Y _ (@euclidean_inner_productP R m)
  NY hNY m _ (@coordinate_basisP R m) Z ev ZN hZ B hB P' k.
have hQ := @finite_inner_polynomial_smooth R (R_n R m) Y _ (@euclidean_inner_productP R m)
  NY hNY m _ (@coordinate_basisP R m) Z ev ZN hZ B hB Q k.
have hQ' := norm_class_higher_scale hN hNY hZ (-1) hQ.
have hsum := norm_class_higher_add hN hNY hZ hP hQ'.
have he : (fun y : X=>P' y-Q y)=(fun x : X=>P' x+(-1)*:Q x).
  by apply/funext=>y; rewrite scaleN1r.
by rewrite he.
Qed.

(** Source for [whitney_difference_summand_class]:
    each summand v_s (P_{xi(s)}-Q) is of class infinity
    on R^m, Federer 3.1.14, p. 226, by the global class
    of v_s from 3.1.13 and the bilinear rule. *)
Lemma whitney_difference_summand_class (Q : PolynomialFunction (R_n R m) Y) s :
  S s -> norm_class_infinity N NY ev ZN (fun _=>True) (whitney_difference_summand Q s).
Proof.
move=>hs k.
have htop : forall x : X, True -> norm_domain_interior N (fun _=>True) x.
  move=>x _; exists 1; split; first exact: ltr01; by move=>u hu.
have hv : norm_class_higher N (fun t : R^o=>`|t|) ew WN (fun _=>True) (v s) k.
  exact: (partition_family_global_smooth hfamily hs k).
have hd := whitney_polynomial_difference_class (P (xi s)) Q htop k.
exact: (@norm_class_higher_bilinear R (R_n R m) N hN k R^o Y Y
  (fun t : R^o=>`|t|) NY NY (@scalar_absolute_value_norm R) hNY hNY
  W Z Z ew WN ev ZN ev ZN hW hZ hZ (fun _=>True) (v s) (fun y : X=>(P (xi s)) y-Q y) _
  (scalar_vector_bounded_bilinear hNY) hv hd).
Qed.

(** Source for [whitney_difference_sum_law]:
    g-Q is on U the locally finite sum of the summands
    v_s (P_{xi(s)}-Q), because sum_s v_s=1 there,
    Federer 3.1.14, p. 226. *)
Lemma whitney_difference_sum_law (Q : PolynomialFunction (R_n R m) Y) :
  is_finite_family_sum_on U S (whitney_difference_summand Q) (fun y : X=>g y-Q y).
Proof.
move=>y hy F hFI hF.
have hfin := norm_locally_finite_active_family
  (norm_partition_locally_finite (partition_family_partition hfamily)).
have [G [hGI hG]] := hfin y hy.
pose F' := (F `|` G)%fset.
have hF'I s : s \in F' -> S s.
  rewrite in_fsetU=>/orP [hs|hs]; [exact: hFI|exact: hGI].
have hvF' s : S s -> s \notin F' -> v s y=0.
  move=>hs; rewrite in_fsetU negb_or=>/andP [_ hn]; exact: hG hs hn.
have hwF' s : S s -> s \notin F' -> whitney_summand P xi v s y=0.
  by move=>hs hn; rewrite /whitney_summand (hvF' s hs hn) scale0r.
have hdF' s : S s -> s \notin F' -> whitney_difference_summand Q s y=0.
  by move=>hs hn; rewrite /whitney_difference_summand (hvF' s hs hn) scale0r.
have hg : g y=\sum_(s <- F') whitney_summand P xi v s y.
  exact: (whitney_extension_sum_law hfamily hy hF'I hwF').
have hone : (1 : R)=\sum_(s <- F') v s y.
  exact: (norm_partition_sum_one (partition_family_partition hfamily) hy hF'I hvF').
have hQ : Q y=\sum_(s <- F') v s y*:Q y.
  by rewrite -scaler_suml -hone scale1r.
have hsplit : g y-Q y=\sum_(s <- F') whitney_difference_summand Q s y.
  rewrite hg hQ -sumrB; apply: eq_bigr=>s _.
  by rewrite /whitney_difference_summand /whitney_summand scalerBr.
rewrite hsplit.
apply: (finite_family_sum_selection_independent hF'I hFI hdF' hF).
Qed.

(** Source for [whitney_derivative_difference_sum]:
    "D^i g(x)-D^i P_b(x)=sum_{s in S_x} sum_j ..." in the
    estimate of Federer 3.1.14, p. 226: the difference of
    the actual differentials of g and of a polynomial Q at
    x in U is the finite sum over S_x of the differentials
    of the summands v_s (P_{xi(s)}-Q), with any global
    differential fields of these summands. *)
Theorem whitney_derivative_difference_sum i x (z zq : Z i)
    (Q : PolynomialFunction (R_n R m) Y) (D : X->X->Z i) :
  U x ->
  has_norm_higher_differential N ev ZN U g i x z ->
  has_norm_higher_differential N ev ZN U Q i x zq ->
  (forall s, S s -> forall y, has_norm_higher_differential N ev ZN (fun _=>True)
    (whitney_difference_summand Q s) i y (D s y)) ->
  z-zq=\sum_(s <- whitney_overlap_fset x) D s x.
Proof.
move=>hx hz hzq hD.
have ho := whitney_family_open hA.
have [hOx [hOU [hOo hmeet]]] := partition_overlap_neighborhood_laws S ho hx.
have hU : forall y, U y -> norm_domain_interior N U y.
  exact: (inner_open_norm_domain (whitney_union_open hA)).
have hvan : forall y, O x y -> forall s, S s -> s \notin whitney_overlap_fset x ->
    whitney_difference_summand Q s y=0.
  move=>y hy s hs hn.
  by rewrite /whitney_difference_summand (whitney_partition_vanishes_off_overlap hx hy hs hn) scale0r.
have hsumD := @norm_local_finite_sum_differential R (R_n R m) Y X N NY hN hNY Z ev ZN hZ
  U (O x) S (whitney_difference_summand Q) (fun y : X=>g y-Q y) (whitney_overlap_fset x)
  i D (@whitney_difference_sum_law Q) (whitney_overlap_fset_member hx) hOU hOo
  hvan hD x hOx.
have hdiff : has_norm_higher_differential N ev ZN U (fun y : X=>g y-Q y) i x (z-zq).
  have hgc : norm_class_higher N NY ev ZN U g i := whitney_extension_class_off hNY hZ hW P xi hfamily hA i.
  have hQc : norm_class_higher N NY ev ZN U Q i.
    exact: (@finite_inner_polynomial_smooth R (R_n R m) Y _ (@euclidean_inner_productP R m)
      NY hNY m _ (@coordinate_basisP R m) Z ev ZN hZ U hU Q i).
  have [Dg [hDg _]] := norm_class_higher_fields hN hNY hZ hgc.
  have [DQ [hDQ _]] := norm_class_higher_fields hN hNY hZ hQc.
  have hgi := hDg i (leqnn i).
  have hQi := hDQ i (leqnn i).
  have hQs := norm_higher_differential_field_scale hN hNY hZ (-1) hQi.
  have hadd := norm_higher_differential_field_add hN hNY hZ hgi hQs hx.
  have hzg : Dg i x=z := norm_higher_differential_unique hN hNY hZ (hgi x hx) hz.
  have hzq' : DQ i x=zq := norm_higher_differential_unique hN hNY hZ (hQi x hx) hzq.
  have he : (fun t : X=>g t+(-1)*:Q t)=(fun y : X=>g y-Q y).
    by apply/funext=>y; rewrite scaleN1r.
  by rewrite he hzg hzq' scaleN1r in hadd.
exact: (norm_higher_differential_unique hN hNY hZ hdiff hsumD).
Qed.
End WhitneyDerivativeSums.
