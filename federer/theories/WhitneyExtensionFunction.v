(** Federer (1969), 3.1.14, pp. 225–226:
    the extension g defined by g(x)=P_x(x) on A and
    g(x)=sum_s v_s(x) P_{xi(s)}(x) on U=R^m-A, through the
    partition of unity of 3.1.13 for the family {U} and the
    nearest points xi(s); g|U is of class infinity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp finmap classical_sets
  cardinality reals topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness RealNormUP
  BoundedHom PolynomialFunctions PolynomialRepresentations
  ContinuousMultilinearUP NormDifferentialUP NormClassHigherUP NormClassHigherFields
  NormBoundedBilinearUP NormClassHigherBilinear NormHigherDifferentialUP
  InnerNearestUP FiniteInnerPolynomialSmoothness
  FiniteFamilySumUP FiniteFamilySumSealed NormLocallyFiniteFamilyUP
  NormPartitionUnityUP NormClassHigherLocallyFiniteSum
  FedererCoverRadius EuclideanPartitionBallCoverUP EuclideanPartitionFamilyUP
  EuclideanPartitionOverlapNeighborhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section WhitneyExtensionFunction.
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
Variable P : X->PolynomialFunction (R_n R m) Y.
Variable xi : X->X.
Hypothesis hxi : forall s, is_inner_nearest (@euclidean_inner_productP R m) s A (xi s).
Local Notation Phi := ([set (~` A : set X)]).
Local Notation U := (\bigcup_(T in Phi) T).
Variable S : set X.
Variables (sigma : X->R) (v : X->X->R).
Hypothesis hS : is_federer_partition_ball_cover Phi S.
Hypothesis hfamily : is_euclidean_partition_family ew WN Phi S sigma v.

(** Source for [whitney_union_complement]:
    the union of the family {U} is U=R^m-A,
    Federer 3.1.14, p. 225. *)
Lemma whitney_union_complement : U=~` A.
Proof.
apply/seteqP; split=>x.
- by move=>[T ->].
- by move=>hx; exists (~` A).
Qed.

(** Source for [whitney_union_open]:
    U is open since A is closed, Federer 3.1.14, p. 225. *)
Lemma whitney_union_open : closed A -> open U.
Proof. move=>hA; rewrite whitney_union_complement; exact: closed_openC. Qed.

(** Source for [whitney_family_open]:
    the single member of the family {U} is open,
    Federer 3.1.14, p. 225. *)
Lemma whitney_family_open : closed A -> forall T, Phi T -> open T.
Proof. by move=>hA T ->; exact: closed_openC. Qed.

(** Source for [whitney_summand]:
    the summand v_s(x) P_{xi(s)}(x) of the extension
    on U, Federer 3.1.14, p. 225. *)
Definition whitney_summand (s x : X) : Y := v s x*:(P (xi s)) x.

(** Source for [whitney_summand_locally_finite]:
    the summands inherit the local finiteness of the
    partition functions, Federer 3.1.14, pp. 225–226. *)
Lemma whitney_summand_locally_finite :
  is_norm_locally_finite_function_family N U S whitney_summand.
Proof.
move=>a ha.
have [O [hOa [hOU [hOo [F [hFI hF]]]]]] :=
  norm_partition_locally_finite (partition_family_partition hfamily) ha.
exists O; split; first exact hOa; split; first exact hOU; split; first exact hOo.
exists F; split; first exact hFI.
move=>x hx s hs hn; by rewrite /whitney_summand (hF x hx s hs hn) scale0r.
Qed.

(** Source for [whitney_summand_finite]:
    finitely many summands are active at each point of U,
    Federer 3.1.14, p. 225. *)
Lemma whitney_summand_finite : finite_active_family_on U S whitney_summand.
Proof. exact: (norm_locally_finite_active_family whitney_summand_locally_finite). Qed.

(** Source for [whitney_sum]:
    the sealed locally finite sum sum_s v_s(x) P_{xi(s)}(x),
    Federer 3.1.14, p. 225. *)
Definition whitney_sum : X->Y :=
  @FiniteFamilySum.value X X Y U S whitney_summand whitney_summand_finite.

(** Source for [whitney_sum_law]:
    the sum laws of the sealed value, Federer 3.1.14, p. 225. *)
Lemma whitney_sum_law : is_finite_family_sum_on U S whitney_summand whitney_sum.
Proof. exact: FiniteFamilySum.laws. Qed.

(** Source for [whitney_extension]:
    "g(x)=P_x(x) for x in A, g(x)=sum_s v_s(x) P_{xi(s)}(x)
    for x in U", Federer 3.1.14, p. 225. *)
Definition whitney_extension (x : X) : Y :=
  if pselect (A x) then (P x) x else whitney_sum x.

(** Source for [whitney_extension_on]:
    the value on A, Federer 3.1.14, p. 225. *)
Lemma whitney_extension_on x : A x -> whitney_extension x=(P x) x.
Proof. by move=>hx; rewrite /whitney_extension; case: pselect. Qed.

(** Source for [whitney_extension_off]:
    the value on U, Federer 3.1.14, p. 225. *)
Lemma whitney_extension_off x : U x -> whitney_extension x=whitney_sum x.
Proof.
move=>hx; rewrite /whitney_extension; case: pselect=>// hA.
by move: hx; rewrite whitney_union_complement=>hx; exfalso; exact: (hx hA).
Qed.

(** Source for [whitney_extension_sum_law]:
    on U the extension is the locally finite sum,
    Federer 3.1.14, p. 225. *)
Lemma whitney_extension_sum_law :
  is_finite_family_sum_on U S whitney_summand whitney_extension.
Proof.
move=>x hx F hFI hF; rewrite (whitney_extension_off hx).
exact: (whitney_sum_law hx hFI hF).
Qed.

(** Source for [scalar_vector_bounded_bilinear]:
    scalar multiplication is a bounded bilinear map
    with constant one, supporting the class of the
    products v_s P_{xi(s)} in Federer 3.1.14, p. 226. *)
Lemma scalar_vector_bounded_bilinear :
  norm_bounded_bilinear (fun t : R^o=>`|t|) NY NY (fun (t : R^o) (y : Y)=>t*:y).
Proof.
split.
- split.
  + move=>y; move=>a s t /=; by rewrite scalerDl scalerA.
  + move=>t; move=>a y w /=; by rewrite scalerDr scalerA mulrC -scalerA.
- exists 1; split; first exact: ler01.
  move=>t y; by rewrite mul1r (real_seminorm_scale hNY.1).
Qed.

(** Source for [whitney_summand_class]:
    each product v_s P_{xi(s)} is of class infinity
    on the open set U, Federer 3.1.14, p. 226,
    from the partition laws of 3.1.13 and the smoothness
    of polynomials on R^m. *)
Lemma whitney_summand_class (hA : closed A) s :
  S s -> norm_class_infinity N NY ev ZN U (whitney_summand s).
Proof.
move=>hs k.
have hU : forall x, U x -> norm_domain_interior N U x.
  exact: (inner_open_norm_domain (whitney_union_open hA)).
have hv : norm_class_higher N (fun t : R^o=>`|t|) ew WN U (v s) k.
  exact: (norm_partition_smooth (partition_family_partition hfamily) hs k).
have hP : norm_class_higher N NY ev ZN U (P (xi s)) k.
  exact: (@finite_inner_polynomial_smooth R (R_n R m) Y _ (@euclidean_inner_productP R m)
    NY hNY m _ (@coordinate_basisP R m) Z ev ZN hZ U hU (P (xi s)) k).
exact: (@norm_class_higher_bilinear R (R_n R m) N hN k R^o Y Y
  (fun t : R^o=>`|t|) NY NY (@scalar_absolute_value_norm R) hNY hNY
  W Z Z ew WN ev ZN ev ZN hW hZ hZ U (v s) (P (xi s)) _
  scalar_vector_bounded_bilinear hv hP).
Qed.

(** Source for [whitney_extension_class_off]:
    "Clearly g|U is of class infinity", Federer 3.1.14,
    p. 226: a locally finite sum of class-infinity
    functions on the open set U. *)
Theorem whitney_extension_class_off (hA : closed A) :
  norm_class_infinity N NY ev ZN U whitney_extension.
Proof.
move=>k.
exact: (norm_class_higher_locally_finite_sum hN hNY hZ whitney_summand_locally_finite
  whitney_extension_sum_law (fun s hs=>whitney_summand_class hA hs k)).
Qed.
End WhitneyExtensionFunction.
