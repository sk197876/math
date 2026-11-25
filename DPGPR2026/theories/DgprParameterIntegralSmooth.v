(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    dgpr_blueprint.tex, proofs of lem:heat_extension(1) and lem:ibp:
    iterated differentiation under the integral sign. A parameter integral
    F(x) = int k(x,y) d nu y is continuous when k(.,y) is continuous and
    locally dominated by a nu summable function; along a line it has the
    derivative int D k(x,y) d nu y. For x in an open subset A of R^n and a
    family of integrands closed under coordinate partial differentiation,
    every member gives a map of class infinity on A, by the coordinate
    criterion of Federer 3.1.11, p. 223, extended here from R^n to open
    subsets of R^n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureVectorIntegralUP
  SummableRealFunctionUP SummableRealArithmetic TotalVectorIntegralArithmetic
  TotalVectorIntegralEstimate TotalVectorDominatedLimit NormDifferentialUP NormDifferentialLocal
  NormClassOneUP NormedCurveDerivativeUP NormDifferentialScalar NormOpenDomainLaws
  NormPartialDerivative GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness EuclideanCoordinateMetric FamilyUpdate ContinuousMultilinearUP
  ContinuousMultilinearNorm ContinuousMultilinearOne ContinuousMultilinearSealed
  ContinuousMultilinearScalarLift NormHigherDifferentialUP NormHigherDifferentialFirst
  NormClassHigherFromDerivative NormRegularity NormRegularityLinearMaps NormRegularityFiniteSum
  ContinuousPartialDifferentiability CoordinateClassSuccessor.
From DPGPR Require Import DgprParameterIntegralDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dgpr_line_linear]: linearity of [R ∋ s ↦ s c], Federer
    1.4.1, p. 17, supporting the blueprint proof of lem:heat_extension(1). *)
Lemma dgpr_line_linear (R : realType) (Z : lmodType R) (c : Z) :
  linear (fun s : R^o => s *: c).
Proof. by move=> a s1 s2; rewrite scalerDl scalerA. Qed.

(** Source for [dgpr_line_hom]: the linear map [R ∋ s ↦ s c] of R into Z,
    the differential of a curve with velocity c, Federer 3.1.1, p. 209,
    first special case; supporting the blueprint proof of
    lem:heat_extension(1). *)
Definition dgpr_line_hom (R : realType) (Z : lmodType R) (c : Z) : Hom R^o Z :=
  @HomMap R R^o Z (fun s : R^o => s *: c) (asboolT (dgpr_line_linear c)).

(** Source for [dgpr_line_homE]: evaluation of [dgpr_line_hom]. *)
Lemma dgpr_line_homE (R : realType) (Z : lmodType R) (c : Z) (s : R) :
  dgpr_line_hom c s = s *: c.
Proof. by []. Qed.

Section ParameterIntegralLine.
Variable R : realType.
Variable T : choiceType.
Variable nu : set T -> \bar R.
Hypothesis hnu : is_measure nu.
Variables X Z : lmodType R.
Variables (NX : X -> R) (NZ : Z -> R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNZ : is_real_norm NZ.
Local Notation has_integral := (@dgpr_has_integral R T nu Z NZ hNZ).

(** Source for [dgpr_parameter_integral_continuous]: continuity of parameter
    integrals in the blueprint proofs of lem:heat_extension(1) and
    lem:classes, by Lebesgue's bounded convergence theorem, Federer 2.4.9,
    p. 85. Suppose A is open, k(.,y) is continuous on A for every y, k is
    dominated near each point of A by a nu summable function, and
    F(x) = int k(x,y) d nu y for x in A. Then F is continuous on A. *)
Theorem dgpr_parameter_integral_continuous (A : set X) (k : X -> T -> Z) (F : X -> Z) :
  (forall x, A x -> norm_domain_interior NX A x) ->
  (forall x, A x -> has_integral (k x) (F x)) ->
  (forall y, norm_class_zero NX NZ A (fun x => k x y)) ->
  (forall x, A x -> exists (r : R) (g : T -> R), 0 < r /\ summable_real_functions nu g /\
    forall h y, NX h < r -> A (x+h) -> NZ (k (x+h) y) <= g y) ->
  norm_class_zero NX NZ A F.
Proof.
move=> hA hF hk hloc a ha; split; first exact: hA.
move=> e he.
have [r [g [hr [[b hgb] hb]]]] := hloc a ha.
have hgg : summable_real_functions nu (fun y => g y + g y).
  by apply: (@summable_real_add R T nu hnu g g); exists b.
have hNX0 : NX 0 = 0 := real_seminorm_zero hNX.1.
have hba y : NZ (k a y) <= g y.
  have h0 : NX 0 < r by rewrite hNX0.
  have hA0 : A (a+0) by rewrite addr0.
  by have := hb 0 y h0 hA0; rewrite addr0.
pose B h := A (a+h) /\ e <= NZ (F (a+h)-F a).
have hc : exists d : R, 0 < d /\ forall h, NX h < d -> ~ B h.
  apply: (@dgpr_sequence_contradiction R X NX B r hr)=> hs hhs.
  pose q n y := k (a+hs n) y.
  have hq n : has_integral (q n) (F (a+hs n)) := hF (a+hs n) (hhs n).2.2.1.
  have hdom n y : NZ (q n y-k a y) <= g y + g y.
    rewrite /q; apply: (le_trans (real_seminorm_triangle hNZ.1 _ _)).
    rewrite (real_seminorm_negate hNZ.1); apply: lerD; last exact: hba.
    exact: (hb (hs n) y (hhs n).1 (hhs n).2.2.1).
  have hpoint : measure_almost_everywhere nu [set y | forall eta : R, 0 < eta ->
      exists N : nat, forall m, (N <= m)%N -> NZ (q m y-k a y) < eta].
    apply: (@measure_almost_everywhere_mono R T nu hnu setT _ _
      (measure_almost_everywhere_true hnu))=> y _ eta heta.
    have [_ hcont] := hk y a ha.
    have [d [hd hd']] := hcont eta heta.
    have [N hN] := dgpr_reciprocal_eventually hd.
    exists N=> m hm.
    exact: (hd' (hs m) (hhs m).2.2.1 (lt_trans (hhs m).2.1 (hN m hm))).
  have [N hN] := @total_vector_integral_dominated_limit R T Z NZ hNZ nu hnu
    q (k a) (fun n => F (a+hs n)) (F a) (fun y => g y + g y) hq (hF a ha) hgg hdom hpoint e he.
  have hsN := hN N (leqnn N).
  have [_ [_ [_ hge]]] := hhs N.
  by have := le_lt_trans hge hsN; rewrite ltxx.
have [d [hd hgood]] := hc.
exists d; split=> // h hAh hh.
rewrite ltNge; apply/negP=> hle; exact: (hgood h hh (conj hAh hle)).
Qed.

(** Source for [dgpr_parameter_integral_directional]: differentiation under
    the integral sign along a line, blueprint proof of lem:heat_extension(1).
    If the curves [s ↦ k(a+s w, y)] have derivatives k'(a+s w, y) bounded by
    a nu summable g for |s| < r, and the integrals exist, then
    [s ↦ int k(a+s w,y) d nu y] has at 0 the derivative int k'(a,y) d nu y. *)
Theorem dgpr_parameter_integral_directional (k k' : X -> T -> Z) (F : X -> Z)
    (z' : Z) (a w : X) (r : R) (g : T -> R) :
  0 < r ->
  (forall t : R, `|t| < r -> has_integral (k (a+t *: w)) (F (a+t *: w))) ->
  has_integral (k' a) z' ->
  (forall (t : R) y, `|t| < r ->
    has_normed_curve_derivative NZ (fun s => k (a+s *: w) y) t (k' (a+t *: w) y)) ->
  summable_real_functions nu g ->
  (forall (t : R) y, `|t| < r -> NZ (k' (a+t *: w) y) <= g y) ->
  has_normed_curve_derivative NZ (fun s => F (a+s *: w)) 0 z'.
Proof.
move=> hr hF hz hd hg hb.
have hR := @scalar_absolute_value_norm R.
pose A' := fun t : R^o => `|t| < r.
pose f' := fun (t : R^o) y => k (a+t *: w) y.
pose Df' := fun (t : R^o) y => dgpr_line_hom (k' (a+t *: w) y).
pose F' := fun t : R^o => F (a+t *: w).
have hA' (h : R^o) : `|h| < r -> A' (0+h) by rewrite /A' add0r.
have hint (h : R^o) : `|h| < r -> has_integral (f' (0+h)) (F' (0+h)).
  by move=> hh; rewrite /f' /F' add0r; exact: hF.
have hL (v : R^o) : has_integral (fun y => Df' 0 y v) (dgpr_line_hom z' v).
  have h := @total_vector_integral_scale R T Z NZ hNZ nu hnu _ _ v hz.
  rewrite /Df' scale0r addr0; exact: h.
have hdiff (h : R^o) y : `|h| < r ->
    has_norm_differential (fun t : R^o => `|t|) NZ A' (fun x => f' x y) (0+h) (Df' (0+h) y).
  move=> hh; apply/(@norm_differential_real_source R Z NZ hNZ A' (fun x => f' x y) (0+h)).
  split.
  - exists (r-`|h|); split; first by rewrite subr_gt0.
    move=> t ht; rewrite /A' add0r.
    apply: (le_lt_trans (ler_normD _ _)); move: ht; rewrite -ltrBrDl; exact.
  - rewrite /Df' dgpr_line_homE scale1r add0r; exact: hd.
have hbound (h : R^o) y (v : R^o) : `|h| < r -> NZ (Df' (0+h) y v) <= g y * `|v|.
  move=> hh; rewrite /Df' dgpr_line_homE (real_seminorm_scale hNZ.1) add0r mulrC.
  by apply: ler_wpM2r; [exact: normr_ge0|exact: hb].
have hD := @dgpr_parameter_integral_differential R T nu hnu R^o Z (fun t : R^o => `|t|) NZ hR hNZ
  A' f' Df' g F' (dgpr_line_hom z') 0 r hr hA' hint hL hdiff hg hbound.
have [_ hcd] := proj1 (@norm_differential_real_source R Z NZ hNZ A' F' 0 (dgpr_line_hom z')) hD.
by move: hcd; rewrite dgpr_line_homE scale1r.
Qed.
End ParameterIntegralLine.

Section CoordinateClassSuccessorOpen.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y : lmodType R.
Variable NY : Y -> R.
Hypothesis hNY : is_real_norm NY.
Local Notation Z := (fun j => @ContinuousMultilinear.space R j X Y N NY hN hNY).
Local Notation ez := (fun j => @ContinuousMultilinear.evaluation R j X Y N NY hN hNY).
Local Notation ZN := (fun j => @ContinuousMultilinear.norm R j X Y N NY hN hNY).
Local Notation hZ := (fun j => @ContinuousMultilinear.laws R j X Y N NY hN hNY).
Local Notation hN1 := (continuous_multilinear_norm_is_norm hNY (hZ 1%N)).

(** Source for [dgpr_class_successor_coordinate_fields]: Federer 3.1.11,
    p. 223, and 3.1.1, p. 211, on an open subset A of R^n: if f is
    continuous on A and has partial derivatives p_i of class k on A, then f
    is of class k+1 on A. This extends the whole-space adapter
    [norm_class_successor_coordinate_fields] of the Federer library, whose
    proof it follows; it supports the blueprint proof of
    lem:heat_extension(1), where A = (0,∞) × R^n. *)
Theorem dgpr_class_successor_coordinate_fields (A : set X) (f : X -> Y)
    (p : 'I_n -> X -> Y) k :
  (forall x, A x -> norm_domain_interior N A x) ->
  norm_class_zero N NY A f ->
  (forall a i, A a -> has_norm_partial_derivative NY f a i (p i a)) ->
  (forall i, norm_class hN hNY A (p i) k) ->
  norm_class hN hNY A f k.+1.
Proof.
move=> hA hF hp hClass.
have [L hL] := coordinate_first_form_lifts_exist n hNY.
pose G := fun a : X => \sum_i L i (p i a).
pose op := @continuous_multilinear_one_operator R X Y (Z 1%N) N NY
  (@ez 1%N) (@ZN 1%N) (hZ 1%N).
have hBasis a j : op (G a) (@coordinate_basis R n j) = p j a.
  change (@ez 1%N [ffun _ : 'I_1 => @coordinate_basis R n j] (G a) = p j a).
  rewrite /G linear_sum (bigD1 j) //=.
  rewrite (hL j).1 !ffunE eqxx scale1r.
  rewrite big1 ?addr0 //.
  move=> i hi; rewrite (hL i).1 !ffunE (negbTE hi) scale0r.
  reflexivity.
have hDifferential a : A a -> has_norm_differential N NY A f a (op (G a)).
  move=> ha.
  apply: (@continuous_partials_differential R n Y NY hNY A f a p (op (G a)) (hBasis a)).
  - have [r [hr hball]] := hA a ha.
    exists r; split=> // x hx.
    have hxa : a+(x-a) = x by rewrite addrC subrK.
    have hAx : A x by rewrite -hxa; apply: hball.
    by split=> // i; exact: hp.
  - move=> i e he.
    have [_ hcont] := (@norm_class_continuous R X Y N NY hN hNY A (p i) k (hClass i)) a ha.
    have [d [hd hBound]] := hcont e he.
    exists d; split=> // x hAx hx.
    have hShift : a+(x-a) = x by rewrite addrC subrK.
    have hAx' : A (a+(x-a)) by rewrite hShift.
    have hPoint := hBound (x-a) hAx' hx.
    by rewrite hShift in hPoint.
have hG : norm_class hN hN1 A G k.
  apply: (@norm_class_finite_sum R X (Z 1%N) N (@ZN 1%N) hN hN1
    A (Finite.clone 'I_n _) (fun i a => L i (p i a)) k hA).
  move=> i; exact: (@norm_class_postcompose_linear R X Y (Z 1%N) N NY (@ZN 1%N)
    hN hNY hN1 A (p i) (L i) k (hL i).2 (hClass i)).
pose W j := @ContinuousMultilinear.space R j X (Z 1%N) N (@ZN 1%N) hN hN1.
pose ew j := @ContinuousMultilinear.evaluation R j X (Z 1%N) N (@ZN 1%N) hN hN1.
pose WN j := @ContinuousMultilinear.norm R j X (Z 1%N) N (@ZN 1%N) hN hN1.
pose hW j := @ContinuousMultilinear.laws R j X (Z 1%N) N (@ZN 1%N) hN hN1.
have hHigher a (ha : A a) : has_norm_higher_differential N ez ZN A f 1%N a (G a).
  exact: (@norm_higher_differential_first R X Y N NY hN hNY Z ez ZN hZ
    A f a (G a)).2 (hDifferential a ha).
exact: (@norm_class_higher_first_field_iff R k X Y N NY hN hNY
  Z ez ZN hZ W ew WN hW A f G hF hHigher).2 hG.
Qed.
End CoordinateClassSuccessorOpen.

Section ParameterIntegralSmooth.
Variable R : realType.
Variable T : choiceType.
Variable nu : set T -> \bar R.
Hypothesis hnu : is_measure nu.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y : lmodType R.
Variable NY : Y -> R.
Hypothesis hNY : is_real_norm NY.
Local Notation has_integral := (@dgpr_has_integral R T nu Y NY hNY).

(** Source for [dgpr_parameter_integral_partial]: differentiation under the
    integral sign in a coordinate direction, blueprint proof of
    lem:heat_extension(1): D_i int k(x,y) d nu y = int D_i k(x,y) d nu y,
    when D_i k(.,y) = k'(.,y) on the open set A and k' is dominated near a
    by a nu summable function. *)
Theorem dgpr_parameter_integral_partial (A : set X) (k k' : X -> T -> Y) (F F' : X -> Y)
    (a : X) (i : 'I_n) :
  A a -> norm_domain_interior N A a ->
  (forall x, A x -> has_integral (k x) (F x)) ->
  has_integral (k' a) (F' a) ->
  (forall x y, A x -> has_norm_partial_derivative NY (fun w => k w y) x i (k' x y)) ->
  (exists (r : R) (g : T -> R), 0 < r /\ summable_real_functions nu g /\
    forall h y, N h < r -> A (a+h) -> NY (k' (a+h) y) <= g y) ->
  has_norm_partial_derivative NY F a i (F' a).
Proof.
move=> ha [r0 [hr0 hball]] hF hF' hp [r [g [hr [hg hb]]]].
pose e := @coordinate_basis R n i.
have hNe : N e = 1.
  exact: (@euclidean_coordinate_unit_norm R n i).
pose rr := Num.min r r0.
have hrr : 0 < rr by rewrite lt_min hr hr0.
have hsmall (t : R) : `|t| < rr -> N (t *: e) < r /\ N (t *: e) < r0.
  rewrite (real_seminorm_scale hN.1) hNe mulr1 lt_min=> /andP [h1 h2]; split=> //.
have hAt (t : R) : `|t| < rr -> A (a+t *: e).
  by move=> ht; apply: hball; exact: (hsmall t ht).2.
have hcurve (t : R) y : `|t| < rr ->
    has_normed_curve_derivative NY (fun s => k (a+s *: e) y) t (k' (a+t *: e) y).
  move=> ht eps heps.
  have [d [hd hd']] := hp (a+t *: e) y (hAt t ht) eps heps.
  exists d; split=> // h hh.
  have hq := hd' h hh.
  have he : a+(t+h) *: e = a+t *: e+h *: e by rewrite scalerDl addrA.
  by rewrite he.
have hD := @dgpr_parameter_integral_directional R T nu hnu X Y NY hNY k k' F (F' a) a e rr g
  hrr (fun t ht => hF _ (hAt t ht)) hF' hcurve hg
  (fun t y ht => hb (t *: e) y (hsmall t ht).1 (hAt t ht)).
move=> eps heps; have [d [hd hd']] := hD eps heps.
exists d; split=> // h hh.
have hq := hd' h hh.
by rewrite add0r scale0r addr0 in hq.
Qed.

(** Source for [dgpr_parameter_integral_smooth]: differentiation under the
    integral sign, iterated, in the blueprint proofs of lem:heat_extension(1)
    and lem:ibp ("e_epsilon is of class infinity"). Suppose A is an open
    subset of R^n and K is a family of integrands k : R^n -> T -> Y such
    that every member is integrable at each point of A, continuous in x on A,
    dominated near each point of A by a nu summable function, and has on A
    coordinate partial derivatives in x that are again members of K. Then
    [x ↦ int k(x,y) d nu y] is of class infinity on A for every k in K. *)
Theorem dgpr_parameter_integral_smooth (A : set X) (K : (X -> T -> Y) -> Prop) :
  (forall x, A x -> norm_domain_interior N A x) ->
  (forall k, K k -> forall x, A x -> exists z, has_integral (k x) z) ->
  (forall k, K k -> forall y, norm_class_zero N NY A (fun x => k x y)) ->
  (forall k, K k -> forall i, exists k', K k' /\
    forall x y, A x -> has_norm_partial_derivative NY (fun w => k w y) x i (k' x y)) ->
  (forall k, K k -> forall x, A x -> exists (r : R) (g : T -> R), 0 < r /\
    summable_real_functions nu g /\ forall h y, N h < r -> A (x+h) -> NY (k (x+h) y) <= g y) ->
  forall k F, K k -> (forall x, A x -> has_integral (k x) (F x)) ->
  norm_class_all_orders hN hNY A F.
Proof.
move=> hA hint hcont hpart hdom k F hk hF m.
elim: m k F hk hF=> [|m IH] k F hk hF.
  apply/(@norm_class_zeroP R X Y N NY hN hNY A F).
  exact: (@dgpr_parameter_integral_continuous R T nu hnu X Y N NY hN hNY A k F
    hA hF (hcont k hk) (hdom k hk)).
have [kp hkp] := choice (hpart k hk).
have hex i x : exists z, A x -> has_integral (kp i x) z.
  case: (pselect (A x))=> [hx|hx]; last by exists 0.
  have [z hz] := hint (kp i) (hkp i).1 x hx; by exists z.
have hex2 i : exists Fi : X -> Y, forall x, A x -> has_integral (kp i x) (Fi x).
  by have [Fi hFi] := choice (hex i); exists Fi.
have [Fp hFp] := choice hex2.
apply: (@dgpr_class_successor_coordinate_fields R n Y NY hNY A F Fp m hA).
- exact: (@dgpr_parameter_integral_continuous R T nu hnu X Y N NY hN hNY A k F
    hA hF (hcont k hk) (hdom k hk)).
- move=> a i ha.
  apply: (@dgpr_parameter_integral_partial A k (kp i) F (Fp i) a i ha (hA a ha) hF
    (hFp i a ha) (hkp i).2).
  exact: (hdom (kp i) (hkp i).1 a ha).
- move=> i; exact: (IH (kp i) (Fp i) (hkp i).1 (hFp i)).
Qed.
End ParameterIntegralSmooth.
