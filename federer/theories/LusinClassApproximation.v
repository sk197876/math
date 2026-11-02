(** Federer (1969), 3.1.15, pp. 227–228:
    if f is of class k on an open set B, A is a subset of B, and
    the kth differential of f has finite upper growth at every
    point of A, then for every epsilon there is a map g of class
    k+1 on the whole space with L^m(A cap {f<>g})<epsilon. The
    proof assembles the closed set F of the good-set module, the
    (k+1)-jets of f on F, the Whitney family law and Whitney's
    extension theorem 3.1.14. The finite upper growth of D^k f at
    a is expressed by a bound M|x-a| on a ball about a, for the
    actual kth differentials. The zero-dimensional source space
    is a single point and is treated by a constant map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness RealNormUP
  PolynomialFunctions PolynomialRepresentations PolynomialTaylor
  ContinuousMultilinearUP ContinuousMultilinearNorm NormDifferentialUP NormClassOneUP
  NormHigherDifferentialUP NormClassHigherUP NormHigherDifferentialConstant
  NormHigherDifferentialFields NormHigherSymmetricFormUP NormJetUP NormJetSealed
  NormJetBaseValue MultilinearSuccessorArguments WhitneyModulusUP WhitneyFormBridge
  WhitneyExtension EuclideanLebesgueDimensions MeasureUP MeasureBasic
  HigherDifferentialCoordinateReconstruction OpenRestrictionZeroExtensionMeasurable
  ContinuousMultilinearSuccessorLift TopDifferentialGoodSet TopDifferentialJetFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ZeroDimension.
Variable R : realType.
Variable n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R 0)).
Local Notation N := (inner_norm (@euclidean_inner_productP R 0)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R 0)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Leb := (@euclidean_lebesgue_measure R 0).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R 0}->Hom (Z i) (R_n R n).
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N NY (@ev i) (@ZN i).

(** Source for [zero_dimension_point]:
    R^0 consists of the single point 0, the degenerate case of
    Federer 3.1.15, p. 227. *)
Lemma zero_dimension_point (x : X) : x=0.
Proof. by apply/ffunP=>i; case: i=>[i hi]; exfalso; move: hi; rewrite ltn0. Qed.

(** Source for [federer_3_1_15_zero]:
    the zero-dimensional case of Federer 3.1.15, p. 227: the
    constant map with value f(0) is of class k+1 and agrees
    with f everywhere. *)
Theorem federer_3_1_15_zero (k : nat) (A : set X) (f : X->R_n R n) (e : R) : 0<e ->
  exists g : X->R_n R n, norm_class_higher N NY ev ZN (fun _=>True) g k.+1 /\
    (Leb (A `\` [set x | f x=g x])<e%:E)%E.
Proof.
move=>he.
exists (fun _=>f 0); split.
- exact: (norm_class_infinity_constant hN hNY hZ (@whitney_whole_space_interior R 0) (f 0) k.+1).
- have -> : A `\` [set x | f x=f 0]=set0.
    apply/seteqP; split=>x; last by [].
    by move=>[_ hn]; exfalso; apply: hn; rewrite /= (zero_dimension_point x).
  by rewrite (measure_empty (euclidean_lebesgue_is_measure R 0)) lte_fin.
Qed.
End ZeroDimension.

Section PositiveDimension.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m.+1)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m.+1)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m.+1)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Leb := (@euclidean_lebesgue_measure R m.+1).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m.+1}->Hom (Z i) (R_n R n).
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N NY (@ev i) (@ZN i).
Variable k : nat.
Variables (A B : set X).
Variable f : X->R_n R n.
Hypothesis hf : norm_class_higher N NY ev ZN B f k.
Hypothesis hAB : A `<=` B.
Hypothesis hgrowth : forall a, A a -> forall z, has_norm_higher_differential N ev ZN B f k a z ->
  exists M r : R, 0<r /\ forall x w, B x -> has_norm_higher_differential N ev ZN B f k x w ->
    N (x-a)<r -> @ZN k (w-z)<=M*N (x-a).

(** Source for [federer_3_1_15_positive]:
    Federer 3.1.15, pp. 227–228, for a source space of positive
    dimension: the closed set F with L^m(A-F)<epsilon, the
    (k+1)-jets P_a of f at the points of F, the hypotheses of
    3.1.14 for them, and the extension g, which agrees with f on
    F since P_a(a)=f(a). *)
Theorem federer_3_1_15_positive (e : R) : 0<e ->
  exists g : X->R_n R n, norm_class_higher N NY ev ZN (fun _=>True) g k.+1 /\
    (Leb (A `\` [set x | f x=g x])<e%:E)%E.
Proof.
move=>he.
have hm := euclidean_lebesgue_is_measure R m.+1.
have [hf0 [Dk [hDfield hDk]]] := hf.
have hDkf : forall x, B x -> has_norm_higher_differential N ev ZN B f k x (Dk x) := hDfield.
have hB : open B := inner_norm_domain_open (fun a ha=>(hf0 a ha).1).
have hgrowth' : forall a, A a -> exists M r : R, 0<r /\
    forall x, B x -> N (x-a)<r -> @ZN k (Dk x-Dk a)<=M*N (x-a).
  move=>a ha; have [M [r [hr hb]]] := hgrowth ha (hDkf a (hAB ha)).
  by exists M, r; split=>// x hx hxr; exact: (hb x (Dk x) hx (hDkf x hx) hxr).
have [iota [hiota_bound hiota_rec]] := higher_differential_coordinate_reconstruction hNY hZ k.
have [F [T [hFc hFB hAF hFdiff [hFcont hFrate]]]] :=
  top_differential_good_set hZ hDkf hDk hAB hB hgrowth' hiota_bound hiota_rec he.
have hzzex : forall a, exists z : Z k.+1, F a ->
    forall u v, @ev k u (T a v)=@ev k.+1 (multilinear_successor_arguments u v) z.
  move=>a; case: (pselect (F a))=>[ha|ha].
  - have [z hz] := continuous_multilinear_successor_lift_exists hN hZ
      (norm_differential_bounded (hFdiff a ha)).
    by exists z.
  - by exists 0=>h; exfalso; exact: ha h.
have [zz hzz] := choice hzzex.
have hzzHD : forall a, F a -> has_norm_higher_differential N ev ZN B f k.+1 a (zz a).
  move=>a ha.
  exact: (norm_higher_differential_field_step hN hNY hZ hDkf (hFdiff a ha) (hzz a ha)).
have hPex : forall a, exists Pa : PolynomialFunction (R_n R m.+1) (R_n R n), F a ->
    is_norm_jet_polynomial N ev ZN B f k.+1 a Pa.
  move=>a; case: (pselect (F a))=>[ha|ha].
  - by exists (NormJet.value hN hNY hZ (hzzHD a ha))=>_; exact: NormJet.laws.
  - by exists 0=>h; exfalso; exact: ha h.
have [P hP] := choice hPex.
have hfam : is_whitney_jet_family NY k.+1 P F :=
  top_differential_jet_family hZ hf hDkf hFc hFB hFdiff hFcont hFrate hzzHD hzz hP.
have [g [hg hgj]] := federer_3_1_14 hNY hZ hfam.
exists g; split; first exact: hg.
have [DP [hDPe hDPd]] := whitney_polynomial_fields_exist hNY hZ.
have hfg : forall a, F a -> f a=g a.
  move=>a ha.
  have [z [hz hev]] := hgj a ha 0%N (leq0n _).
  have hz' : @ev 0%N [ffun i : 'I_0=>(0:X)] z=g a := hz.2.
  have hDP0 : @ev 0%N [ffun i : 'I_0=>(0:X)] (DP (P a) 0%N a)=polynomial_function (P a) a := (hDPd (P a) 0%N a).2.
  rewrite -hz' hev -(hDPe (P a) 0%N a [ffun i : 'I_0=>(0:X)]) hDP0.
  exact: esym (norm_jet_base_value hN hNY hZ (hP a ha)).
have hsub : A `\` [set x | f x=g x] `<=` A `\` F.
  by move=>x [hx hn]; split=>// hF; apply: hn; exact: hfg.
exact: (le_lt_trans (measure_mono hm hsub) hAF).
Qed.
End PositiveDimension.

(** Source for [federer_3_1_15]:
    Theorem 3.1.15, Federer, p. 227, in every finite source
    dimension: if A is a subset of B, f : B -> R^n is of class k
    and lim sup ||D^k f(x)-D^k f(a)||/|x-a|<infinity whenever a
    is in A, then for each epsilon>0 there is a map g : R^m -> R^n
    of class k+1 with L^m(A cap {x : f(x)<>g(x)})<epsilon. The
    finite upper limit is stated as a bound M|x-a| on a ball about
    a for the actual kth differentials. *)
Theorem federer_3_1_15 (R : realType) (m n : nat)
    (Z : nat->lmodType R) (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) (R_n R n))
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) (@ev i) (@ZN i))
    (k : nat) (A B : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m)->R_n R n) :
  norm_class_higher (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) ev ZN B f k ->
  A `<=` B ->
  (forall a, A a -> forall z,
    has_norm_higher_differential (inner_norm (@euclidean_inner_productP R m)) ev ZN B f k a z ->
    exists M r : R, 0<r /\ forall x w, B x ->
      has_norm_higher_differential (inner_norm (@euclidean_inner_productP R m)) ev ZN B f k x w ->
      inner_norm (@euclidean_inner_productP R m) (x-a)<r ->
      @ZN k (w-z)<=M*inner_norm (@euclidean_inner_productP R m) (x-a)) ->
  forall e : R, 0<e ->
  exists g : inner_metric_space (@euclidean_inner_productP R m)->R_n R n,
    norm_class_higher (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) ev ZN (fun _=>True) g k.+1 /\
    (@euclidean_lebesgue_measure R m (A `\` [set x | f x=g x])<e%:E)%E.
Proof.
case: m Z ev ZN hZ A B f=>[|m'] Z ev ZN hZ A B f hf hAB hgrowth e he.
- exact: (@federer_3_1_15_zero R n Z ev ZN hZ k A f e he).
- exact: (@federer_3_1_15_positive R m' n Z ev ZN hZ k A B f hf hAB hgrowth e he).
Qed.
