(** Federer (1969), 4.1.12, p. 369:
    the original finite psi_M have
    M(psi_M)<=1 and M(d psi_M)<=2,
    uniformly in M. Their actual
    summand supports are disjoint in
    the first scalar factor. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap CurrentCartesianDomain
  CurrentSpaces CurrentCoefficientNorms CurrentSupportGeometry CurrentTestExteriorDerivative CurrentGlobalComassSealed
  CurrentGlobalComassBound CurrentCartesianTestProductSealed CurrentCartesianTestProductSupport CurrentTestScalarSupport
  CurrentTestFiniteDisjointBounds WeightedIntervalCutoffSealed WeightedIntervalCutoffSupport
  WeightedIntervalProductTests WeightedIntervalProductTestTermBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section WeightedIntervalProductTestBounds.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation AB := (@euclidean_cartesian_set R 1%N 1%N Full Full).
Local Notation hAB := (@current_cartesian_domain_open R 1%N 1%N Full Full hFull hFull).
Local Notation vc d := (@current_test_value R h2 (1+1)%N AB hAB d).
Local Notation NC d := (@current_form_comass R h2 (1+1)%N d).
Local Notation dc := (@current_test_exterior_derivative R h2 (1+1)%N 0%N AB hAB).
Local Notation term := (@weighted_interval_product_test_term R h2).
Local Notation psi := (@weighted_interval_product_test R h2).
Local Notation phi := (@WeightedIntervalCutoff.value R h2).
Local Notation support := (@current_test_support R h2 (1+1)%N 0%N AB hAB).

(** Source for [weighted_interval_product_test_support_unique]:
    no product point lies in
    two distinct original weighted test
    summand supports, supporting Federer
    4.1.12, p. 369. *)
Lemma weighted_interval_product_test_support_unique z i j:
  support (term i) z->support (term j) z->i=j.
Proof.
move=>hi hj.
have hI:=@current_test_scalar_support_subset R h2 (1+1)%N 0%N AB hAB _ _ z hi.
have hJ:=@current_test_scalar_support_subset R h2 (1+1)%N 0%N AB hAB _ _ z hj.
have hPI:=@current_cartesian_test_product_support R h2 1%N 1%N Full Full hFull hFull
  0%N 0%N (phi i) (phi i) z hI.
have hPJ:=@current_cartesian_test_product_support R h2 1%N 1%N Full Full hFull hFull
  0%N 0%N (phi j) (phi j) z hJ.
exact:(@weighted_interval_cutoff_support_unique R h2 _ i j hPI.1 hPJ.1).
Qed.

(** Source for [weighted_interval_product_test_point_bounds]:
    the actual original psi_M retains
    both pointwise bounds, uniformly in
    M, including the empty finite sum,
    supporting Federer 4.1.12, p. 369. *)
Theorem weighted_interval_product_test_point_bounds M z:
  AB z->NC 0%N (vc 0%N (psi M) z)<=1 /\
    NC 1%N (vc 1%N (dc (psi M)) z)<=2.
Proof.
move=>hz.
apply:(@current_test_finite_disjoint_comass_bounds R h2 (1+1)%N 0%N AB hAB 'I_M
  (fun i=>term (val i)) 1 2 (@ler01 R) (ltac:(by rewrite ler0n)) _ _ _ z hz).
- move=>x hx i j hi hj;apply:val_inj.
  exact:weighted_interval_product_test_support_unique hi hj.
- move=>i x hx;exact:weighted_interval_product_test_term_comass hx.
- move=>i x hx;exact:weighted_interval_product_test_term_derivative_comass hx.
Qed.

(** Source for [weighted_interval_product_test_global_bounds]:
    precisely the two displayed original
    global bounds M(psi_M)<=1 and
    M(d psi_M)<=2, Federer 4.1.12,
    p. 369. *)
Theorem weighted_interval_product_test_global_bounds M:
  (@CurrentGlobalComass.value R h2 (1+1)%N 0%N AB (vc 0%N (psi M))<=1%:E)%E /\
  (@CurrentGlobalComass.value R h2 (1+1)%N 1%N AB (vc 1%N (dc (psi M)))<=2%:E)%E.
Proof.
split.
- apply:(@current_global_comass_bound R h2 (1+1)%N 0%N AB (vc 0%N (psi M)) 1).2=>z hz.
  exact:(weighted_interval_product_test_point_bounds M hz).1.
- apply:(@current_global_comass_bound R h2 (1+1)%N 1%N AB (vc 1%N (dc (psi M))) 2).2=>z hz.
  exact:(weighted_interval_product_test_point_bounds M hz).2.
Qed.
End WeightedIntervalProductTestBounds.
