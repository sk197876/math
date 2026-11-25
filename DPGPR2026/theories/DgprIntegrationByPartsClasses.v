(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    section 3, lem:ibp, DPGPR (3.17), first case of the proof, with the
    hypotheses of the blueprint: rho of class infinity, positive, of
    Gaussian decay, with D log rho of polynomial growth, and e of class
    infinity with e, De and D^2 e of polynomial growth. The file passes
    from these class infinity hypotheses (Federer 3.1.11: higher
    differentials, their symmetry and norms; 3.1.1(3) with the
    derivative of log) to the first order fields of [dgpr_ibp_smooth]. *)
From mathcomp Require Import all_boot all_order all_algebra perm boolp classical_sets reals
  constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness FiniteCoordinates
  NormDifferentialUP NormDifferentialDirectional NormDifferentialChain NormClassOneUP
  NormClassZeroPostcompose ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm ContinuousMultilinearZero ContinuousMultilinearOne
  ContinuousMultilinearEvaluationBound MultilinearSuccessorArguments MultilinearArguments
  ConcatenatedFamilies FiniteArgumentPermutation NormHigherDifferentialUP
  NormHigherDifferentialFirst NormHigherDifferentialSymmetry NormHigherDifferentialUnique
  NormClassHigherUP NormRegularity NormDifferentialLinear ProductInnerDifferential NormDifferentialLocal
  RealExponentialUP RealExponentialSealed RealExponentialLaws RealLogarithmDifferential
  EuclideanLebesgueDimensions MeasureUP MeasurableFunctionUP MeasureIntegralUP
  SummableRealFunctionUP.
From DPGPR Require Import DgprGrowthClasses DgprDifferentialCalculus DgprDivergenceIntegral
  DgprIntegrationByParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dgpr_two_arguments]: the pair (w, v) as the family of
    two arguments obtained by adjoining v to (w), Federer 3.1.11, p. 219. *)
Lemma dgpr_two_arguments (T : Type) (w v : T) :
  multilinear_successor_arguments [ffun _ : 'I_1 => w] v =
    [ffun i : 'I_2 => if val i == 0%N then w else v].
Proof.
apply/ffunP=> i; rewrite [RHS]ffunE /multilinear_successor_arguments /multilinear_arguments_cast ffunE.
rewrite /multilinear_arguments_join ffunE /concatenate_family.
case: splitP=> j /= hj; rewrite ffunE.
- by case: i hj=> [[|m] hm] //= hj; have := ltn_ord j; rewrite -hj.
- by case: i hj=> [[|m] hm] //= hj.
Qed.

Section SecondOrder.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (Y : lmodType R) (NY : Y -> R).
Hypothesis hNY : is_real_norm NY.
Local Notation Zk k := (@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ev k := (@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN k := (@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation lawsk k := (@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Local Notation one_op z := (@continuous_multilinear_one_operator R X Y (Zk 1) NX NY
  (ev 1) (ZN 1) (lawsk 1) z).
Local Notation args1 w := ([ffun _ : 'I_1 => w]).
Local Notation args2 w v := (multilinear_successor_arguments [ffun _ : 'I_1 => w] v).

(** Source for [dgpr_first_from_second]: D^1 f(x) exists wherever
    D^2 f(x) exists, by the recursive definition of Federer 3.1.11,
    p. 219. *)
Lemma dgpr_first_from_second (f : X -> Y) (D2 : X -> Zk 2) :
  (forall x, dgpr_higher_differential hNX hNY setT f 2 x (D2 x)) ->
  exists D1 : X -> Zk 1, forall x, dgpr_higher_differential hNX hNY setT f 1 x (D1 x).
Proof.
move=> hD2.
have hex x : exists w : Zk 1, dgpr_higher_differential hNX hNY setT f 1 x w.
  have [g [hg [L [hL _]]]] := hD2 x.
  exact: (norm_domain_interior_member hNX (norm_differential_interior hL)).
by case: (choice hex)=> D1 hD1; exists D1.
Qed.

(** Source for [dgpr_first_differential_operator]: D^1 f(x) acts as the
    differential Df(x), Federer 3.1.11, p. 219, and 3.1.1, p. 209. *)
Lemma dgpr_first_differential_operator (f : X -> Y) (x : X) (z : Zk 1) :
  dgpr_higher_differential hNX hNY setT f 1 x z ->
  has_norm_differential NX NY setT f x (one_op z).
Proof.
move=> h; exact: ((@norm_higher_differential_first R X Y NX NY hNX hNY
  (fun k => Zk k) (fun k => ev k) (fun k => ZN k) (fun k => lawsk k) setT f x z).1 h).
Qed.

(** Source for [dgpr_second_differential_fields]: if D^1 f and D^2 f
    exist everywhere, then [y ↦ Df(y)(w)] has at x the differential
    [v ↦ D^2 f(x)(w, v)], Federer 3.1.11, p. 219. *)
Lemma dgpr_second_differential_fields (f : X -> Y) (D1 : X -> Zk 1) (D2 : X -> Zk 2) :
  (forall x, dgpr_higher_differential hNX hNY setT f 1 x (D1 x)) ->
  (forall x, dgpr_higher_differential hNX hNY setT f 2 x (D2 x)) ->
  exists E : X -> Hom X (Hom X Y),
    (forall x w, dgpr_differential_values NY (fun y => one_op (D1 y) w) x
       (fun v => E x v w)) /\
    (forall x v w, E x v w = ev 2 (args2 w v) (D2 x)).
Proof.
move=> hD1 hD2.
have hZ1 := continuous_multilinear_norm_is_norm hNY (lawsk 1).
have hL a : exists L : Hom X (Zk 1), has_norm_differential NX (ZN 1) setT D1 a L /\
    forall u v, ev 1 u (L v) = ev 2 (multilinear_successor_arguments u v) (D2 a).
  have [g [hg [L [hL hev]]]] := hD2 a.
  have hgD : g = D1 by apply: funext=> x; exact: hg x (D1 x) (hD1 x).
  exists L; split=> //.
  rewrite -hgD; case: hL=> _ hLb hLr; split=> //.
  - by exists 1; split.
  - move=> e he; have [d [hd hr]] := hLr e he.
    by exists d; split=> // h _ hh; apply: hr=> //; exists (D1 (a + h)); exact: hD1.
case: (choice hL)=> L hLL.
pose E x : Hom X (Hom X Y) := hom_comp (@continuous_multilinear_one_evaluation R X Y (Zk 1)
  NX NY (ev 1) (ZN 1) (lawsk 1)) (L x).
have hE x v w : E x v w = ev 2 (args2 w v) (D2 x).
  have [_ hev] := hLL x; rewrite -hev; reflexivity.
exists E; split; last exact: hE.
move=> x w; have [hLx _] := hLL x.
have hM := continuous_multilinear_evaluation_bounded hNX (lawsk 1) (args1 w).
exists (hom_comp (ev 1 (args1 w)) (L x)); split.
- exact: (norm_differential_postcompose_linear hNX hZ1 hNY hM hLx).
- by move=> v; rewrite hom_compE hE; have [_ hev] := hLL x; rewrite hev.
Qed.

(** Source for [dgpr_second_differential_symmetric]: D^2 f(x) is
    symmetric, Federer 3.1.11, p. 220. *)
Lemma dgpr_second_differential_symmetric (f : X -> Y) (x : X) (z : Zk 2) (v w : X) :
  dgpr_higher_differential hNX hNY setT f 2 x z ->
  ev 2 (args2 w v) z = ev 2 (args2 v w) z.
Proof.
move=> h.
have hs := @norm_higher_differential_symmetric R X Y NX NY hNX hNY
  (fun k => Zk k) (fun k => ev k) (fun k => ZN k) (fun k => lawsk k) setT f 2 x z h
  (tperm (0 : 'I_2) 1) (args2 v w).
rewrite -hs; congr (ev 2 _ z).
apply/ffunP=> i; rewrite /finite_argument_permutation !dgpr_two_arguments !ffunE.
by case: i=> [[|[|m]] hm] //=; rewrite permE.
Qed.

(** Source for [dgpr_first_bound]: |D^1 f(x)(v)| <= ||D^1 f(x)|| |v|,
    the norm of Federer 3.1.11, p. 219. *)
Lemma dgpr_first_bound (z : Zk 1) (v : X) : NY (ev 1 (args1 v) z) <= ZN 1 z * NX v.
Proof.
have hb := multilinear_operator_bound (continuous_multilinear_norm_laws (lawsk 1) z) (args1 v).
by rewrite big_ord1 ffunE in hb.
Qed.

(** Source for [dgpr_second_bound]: |D^2 f(x)(w, v)| <= ||D^2 f(x)|| |v| |w|,
    the norm of Federer 3.1.11, p. 219. *)
Lemma dgpr_second_bound (z : Zk 2) (v w : X) : NY (ev 2 (args2 w v) z) <= ZN 2 z * (NX v * NX w).
Proof.
have hb := multilinear_operator_bound (continuous_multilinear_norm_laws (lawsk 2) z) (args2 w v).
have hp : \prod_(j < 2) NX (args2 w v j) = NX v * NX w.
  rewrite /multilinear_successor_arguments multilinear_arguments_cast_product
    multilinear_arguments_product big_ord1 ffunE big_ord1 ffunE mulrC.
  by [].
by rewrite hp in hb.
Qed.

(** Source for [dgpr_zeroth_differential]: D^0 f(x) is f(x) and has the
    norm |f(x)|, Federer 3.1.11, p. 219, with the norm of the erratum to
    p. 219. *)
Lemma dgpr_zeroth_differential (f : X -> Y) (x : X) :
  exists z : Zk 0, dgpr_higher_differential hNX hNY setT f 0 x z /\ ZN 0 z = NY (f x).
Proof.
have [z hz] := @continuous_multilinear_zero_surjective R X Y (Zk 0) NX NY hNY (ev 0) (ZN 0)
  (lawsk 0) (f x).
exists z; split; first by split.
by rewrite (@continuous_multilinear_zero_norm R X Y (Zk 0) NX NY hNY (ev 0) (ZN 0) (lawsk 0) z) hz.
Qed.

(** Source for [dgpr_class_second_continuous]: for f of class 2, the map
    [x ↦ D^2 f(x)(w, v)] is continuous, Federer 3.1.11, p. 220. *)
Lemma dgpr_class_second_continuous (f : X -> Y) (D2 : X -> Zk 2) (v w : X) :
  norm_class hNX hNY setT f 2 ->
  (forall x, dgpr_higher_differential hNX hNY setT f 2 x (D2 x)) ->
  norm_class_zero NX NY setT (fun x => ev 2 (args2 w v) (D2 x)).
Proof.
move=> [_ [D [hD hc]]] hD2.
have he : D = D2.
  apply: funext=> x.
  exact: (@norm_higher_differential_unique R X Y NX NY hNX hNY (fun k => Zk k)
    (fun k => ev k) (fun k => ZN k) (fun k => lawsk k) setT f 2 x _ _ (hD x Logic.I) (hD2 x)).
rewrite -he.
have hZ2 := continuous_multilinear_norm_is_norm hNY (lawsk 2).
have hM := continuous_multilinear_evaluation_bounded hNX (lawsk 2) (args2 w v).
exact: (norm_class_zero_postcompose hZ2 hc hM).
Qed.
End SecondOrder.

Section Bridges.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation NR := (fun t : R^o => `|t|).
Local Notation hNR := (@scalar_absolute_value_norm R).
Local Notation L := (@RealExponential.logarithm R).
Local Notation pw := dgpr_polynomial_weight.
Local Notation gw := dgpr_gaussian_weight.
Local Notation ZR k := (@ContinuousMultilinear.space R k X R^o NX NR hNX hNR).
Local Notation evR k := (@ContinuousMultilinear.evaluation R k X R^o NX NR hNX hNR).
Local Notation ZNR k := (@ContinuousMultilinear.norm R k X R^o NX NR hNX hNR).
Local Notation lawsR k := (@ContinuousMultilinear.laws R k X R^o NX NR hNX hNR).
Local Notation ZX k := (@ContinuousMultilinear.space R k X X NX NX hNX hNX).
Local Notation evX k := (@ContinuousMultilinear.evaluation R k X X NX NX hNX hNX).
Local Notation ZNX k := (@ContinuousMultilinear.norm R k X X NX NX hNX hNX).
Local Notation lawsX k := (@ContinuousMultilinear.laws R k X X NX NX hNX hNX).
Local Notation args2 w v := (multilinear_successor_arguments [ffun _ : 'I_1 => w] v).

(** Source for [dgpr_log_derivative_polynomial_growth]: the hypothesis
    "D log rho has polynomial growth" of lem:ibp, blueprint section 3,
    with def:classes: log rho is of class infinity, so that D log rho is,
    and ||D^j log rho(x)|| <= c (1 + |x|)^c for j >= 1 and x in R^n. *)
Definition dgpr_log_derivative_polynomial_growth (rho : X -> R) :=
  norm_class_all_orders hNX hNR setT (fun x => L (rho x)) /\
  forall j, (0 < j)%N -> exists c, 0 < c /\
    dgpr_derivative_bounded hNX hNR setT setT (fun x => L (rho x)) j
      (fun x => pw c (NX x)).

(** Source for [dgpr_second_order_polynomial_growth]: the hypothesis of
    the first case in the proof of lem:ibp, blueprint section 3: e is of
    class infinity and |e(x)|, ||De(x)||, ||D^2 e(x)|| <= c (1 + |x|)^c. *)
Definition dgpr_second_order_polynomial_growth (e : X -> X) :=
  norm_class_all_orders hNX hNX setT e /\ exists c, 0 < c /\
    forall j, (j <= 2)%N ->
      dgpr_derivative_bounded hNX hNX setT setT e j (fun x => pw c (NX x)).

(** Source for [dgpr_setT_conj]: the domain of a composite of maps
    defined everywhere is everything, Federer 3.1.1, p. 210. *)
Lemma dgpr_setT_conj (T U : Type) (g : T -> U) :
  (fun x => setT x /\ setT (g x)) = (setT : set T).
Proof. by apply: funext=> x; apply: propext; split. Qed.

(** Source for [dgpr_log_density_fields]: the hypotheses of lem:ibp on
    rho give the first order data used in its proof: rho <= c exp(-|x|^2/c),
    D rho = rho D log rho (Federer 3.1.1(3) with the derivative of log),
    D^2 log rho(x)(w, v) as the differential of [y ↦ D log rho(y)(w)],
    its continuity, and the polynomial bounds, Federer 3.1.11. *)
Lemma dgpr_log_density_fields (rho : X -> R) (Dh : X -> Hom X R^o) (D2h : X -> ZR 2) :
  dgpr_gaussian_decay hNR rho -> (forall x, 0 < rho x) ->
  dgpr_log_derivative_polynomial_growth rho ->
  (forall x, has_norm_differential NX NR setT (fun y => L (rho y)) x (Dh x)) ->
  (forall x, dgpr_higher_differential hNX hNR setT (fun y => L (rho y)) 2 x (D2h x)) ->
  exists (c : R) (H2 : X -> Hom X (Hom X R^o)), 0 < c /\
    (forall x, rho x <= gw c (NX x)) /\
    (forall x, dgpr_differential_values NR rho x (fun v => rho x * Dh x v)) /\
    (forall x w, dgpr_differential_values NR (fun y => Dh y w) x (fun v => H2 x v w)) /\
    (forall x v w, H2 x v w = evR 2 (args2 w v) (D2h x)) /\
    (forall v w, norm_class_zero NX NR setT (fun x => H2 x v w)) /\
    (forall x v w, `|Dh x v| <= pw c (NX x) * NX v /\
       `|H2 x v w| <= pw c (NX x) * (NX v * NX w)).
Proof.
move=> [hrc hdec] hpos [hhc hhg] hDh hD2h.
have hN := inner_norm_nonnegative (@euclidean_inner_productP R n).
have [c0 [hc0 hb0]] := hdec 0%N.
have [c1 [hc1 hb1]] := hhg 1%N isT.
have [c2 [hc2 hb2]] := hhg 2%N isT.
have [D1 hD1] := dgpr_first_from_second hD2h.
have hDh1 x : Dh x = @continuous_multilinear_one_operator R X R^o (ZR 1) NX NR
    (evR 1) (ZNR 1) (lawsR 1) (D1 x).
  exact: (norm_differential_unique hNX hNR (hDh x)
    (dgpr_first_differential_operator (hD1 x))).
have [E [hE hEv]] := dgpr_second_differential_fields hD1 hD2h.
have [Drho hDrho] := (norm_class_firstP hNX hNR setT rho).1 (hrc 1%N).
have hDr x : has_norm_differential NX NR setT rho x (Drho x).
  exact: (norm_class_one_differential hDrho (Logic.I : setT x)).
have hDhr x v : rho x * Dh x v = Drho x v.
  have hG := norm_differential_chain hNX hNR hNR (hDr x) (real_logarithm_differential (hpos x)).
  rewrite dgpr_setT_conj in hG.
  rewrite (norm_differential_unique hNX hNR (hDh x) hG) hom_compE.
  change (rho x * ((rho x)^-1 * Drho x v) = Drho x v).
  by rewrite mulrA mulfV ?mul1r // gt_eqF.
pose c := c0 + c1 + c2.
have hc : 0 < c by rewrite /c; lra.
have hc1c : c1 <= c by rewrite /c; lra.
have hc2c : c2 <= c by rewrite /c; lra.
exists c, E; split=> //; split.
  move=> x; have [z [hz hzn]] := dgpr_zeroth_differential hNR rho x.
  have h0 := hb0 x z Logic.I hz; rewrite hzn in h0.
  apply: le_trans (ler_norm (rho x)) _; apply: le_trans h0 _.
  by apply: dgpr_gaussian_weight_constant=> //; rewrite /c; lra.
split.
  by move=> x; exists (Drho x); split=> // v; rewrite hDhr.
split.
  move=> x w; apply: (dgpr_values_ext _ _ (hE x w))=> [y|v] //.
  by rewrite hDh1.
split; first exact: hEv.
split.
  move=> v w; have hh := dgpr_class_second_continuous v w (hhc 2%N) hD2h.
  have -> : (fun x => E x v w) = (fun x => evR 2 (args2 w v) (D2h x)).
    by apply: funext=> x; rewrite hEv.
  exact: hh.
move=> x v w; split.
- rewrite hDh1; apply: le_trans (dgpr_first_bound (D1 x) v) _.
  apply: ler_wpM2r; first exact: hN.
  apply: le_trans (hb1 x (D1 x) Logic.I (hD1 x)) _.
  exact: dgpr_polynomial_weight_constant (ltW hc1) hc1c (hN x).
- rewrite hEv; apply: le_trans (dgpr_second_bound (D2h x) v w) _.
  apply: ler_wpM2r; first exact: mulr_ge0 (hN v) (hN w).
  apply: le_trans (hb2 x (D2h x) Logic.I (hD2h x)) _.
  exact: dgpr_polynomial_weight_constant (ltW hc2) hc2c (hN x).
Qed.

(** Source for [dgpr_second_order_fields]: for e as in the first case of
    the proof of lem:ibp, the fields De and D^2 e give the first order
    data used there: [y ↦ De(y)(w)] has the differential
    [v ↦ D^2 e(x)(w, v)], D^2 e(x) is symmetric, and the bounds hold,
    Federer 3.1.11. *)
Lemma dgpr_second_order_fields (e : X -> X) (De : X -> Hom X X) :
  dgpr_second_order_polynomial_growth e ->
  (forall x, has_norm_differential NX NX setT e x (De x)) ->
  exists (c : R) (E2 : X -> Hom X (Hom X X)), 0 < c /\
    (forall x, dgpr_differential_values NX e x (fun v => De x v)) /\
    (forall x w, dgpr_differential_values NX (fun y => De y w) x (fun v => E2 x v w)) /\
    (forall x v w, E2 x v w = E2 x w v) /\
    (forall x v w, NX (e x) <= pw c (NX x) /\ NX (De x v) <= pw c (NX x) * NX v /\
       NX (E2 x v w) <= pw c (NX x) * (NX v * NX w)).
Proof.
move=> [hec [c [hc hb]]] hDe.
have hN := inner_norm_nonnegative (@euclidean_inner_productP R n).
have [_ [D2 [hD2 _]]] := hec 2%N.
have hD2' x : dgpr_higher_differential hNX hNX setT e 2 x (D2 x) := hD2 x Logic.I.
have [D1 hD1] := dgpr_first_from_second hD2'.
have hDe1 x : De x = @continuous_multilinear_one_operator R X X (ZX 1) NX NX
    (evX 1) (ZNX 1) (lawsX 1) (D1 x).
  exact: (norm_differential_unique hNX hNX (hDe x)
    (dgpr_first_differential_operator (hD1 x))).
have [E [hE hEv]] := dgpr_second_differential_fields hD1 hD2'.
exists c, E; split=> //; split.
  by move=> x; exists (De x); split.
split.
  move=> x w; apply: (dgpr_values_ext _ _ (hE x w))=> [y|v] //.
  by rewrite hDe1.
split.
  by move=> x v w; rewrite !hEv; exact: (dgpr_second_differential_symmetric v w (hD2' x)).
move=> x v w; split; [|split].
- have [z [hz hzn]] := dgpr_zeroth_differential hNX e x.
  by rewrite -hzn; exact: hb 0%N isT x z Logic.I hz.
- rewrite hDe1; apply: le_trans (dgpr_first_bound (D1 x) v) _.
  apply: ler_wpM2r; first exact: hN.
  exact: hb 1%N isT x (D1 x) Logic.I (hD1 x).
- rewrite hEv; apply: le_trans (dgpr_second_bound (D2 x) v w) _.
  apply: ler_wpM2r; first exact: mulr_ge0 (hN v) (hN w).
  exact: hb 2%N isT x (D2 x) Logic.I (hD2' x).
Qed.

(** Source for [dgpr_ibp_smooth_classes]: lem:ibp, DPGPR (3.17), in the
    first case of the blueprint proof: rho is of class infinity,
    positive, of Gaussian decay, D log rho has polynomial growth, and e is
    of class infinity with e, De, D^2 e of polynomial growth. Then
    - ∫ rho D^2 log rho(e, e) dL^n
      = ∫ rho [(div e + D log rho(e))^2 - trace(De ∘ De)] dL^n,
    both integrands being L^n summable. Here Dh(x) = D log rho(x),
    D2h(x) = D^2 log rho(x) and De(x) = De(x), for any such fields. *)
Theorem dgpr_ibp_smooth_classes (rho : X -> R) (e : X -> X) (Dh : X -> Hom X R^o)
    (D2h : X -> ZR 2) (De : X -> Hom X X) :
  dgpr_gaussian_decay hNR rho -> (forall x, 0 < rho x) ->
  dgpr_log_derivative_polynomial_growth rho ->
  dgpr_second_order_polynomial_growth e ->
  (forall x, has_norm_differential NX NR setT (fun y => L (rho y)) x (Dh x)) ->
  (forall x, dgpr_higher_differential hNX hNR setT (fun y => L (rho y)) 2 x (D2h x)) ->
  (forall x, has_norm_differential NX NX setT e x (De x)) ->
  exists a : R,
    is_measure_integral mu (real_total_integrand
      (fun x => - (rho x * evR 2 [ffun _ : 'I_2 => e x] (D2h x)))) a%:E /\
    is_measure_integral mu (real_total_integrand
      (fun x => rho x * ((dgpr_divergence (De x) + Dh x (e x)) ^+ 2 -
        dgpr_divergence (hom_comp (De x) (De x))))) a%:E.
Proof.
move=> hrho hpos hlog he hDh hD2h hDe.
have hN := inner_norm_nonnegative (@euclidean_inner_productP R n).
have [c1 [H2 [hc1 [hrg [hdr [hH2 [hH2v [hH2c hHb]]]]]]]] :=
  dgpr_log_density_fields hrho hpos hlog hDh hD2h.
have [c2 [E2 [hc2 [hdv [hE2 [hsym hEb]]]]]] := dgpr_second_order_fields he hDe.
pose c := c1 + c2.
have hc : 0 < c by rewrite /c; lra.
have hw1 r : 0 <= r -> pw c1 r <= pw c r.
  by move=> hr; apply: dgpr_polynomial_weight_constant=> //; [exact: ltW|rewrite /c; lra].
have hw2 r : 0 <= r -> pw c2 r <= pw c r.
  by move=> hr; apply: dgpr_polynomial_weight_constant=> //; [exact: ltW|rewrite /c; lra].
have hg x : rho x <= gw c (NX x).
  by apply: le_trans (hrg x) _; apply: dgpr_gaussian_weight_constant=> //; rewrite /c; lra.
have hb x v w : NX (e x) <= pw c (NX x) /\ NX (De x v) <= pw c (NX x) * NX v /\
    NX (E2 x v w) <= pw c (NX x) * (NX v * NX w) /\ `|Dh x v| <= pw c (NX x) * NX v /\
    `|H2 x v w| <= pw c (NX x) * (NX v * NX w).
  have [h1 [h2 h3]] := hEb x v w; have [h4 h5] := hHb x v w.
  have hv := hN v; have hvw := mulr_ge0 (hN v) (hN w).
  split; first exact: le_trans h1 (hw2 _ (hN x)).
  split; first exact: le_trans h2 (ler_wpM2r hv (hw2 _ (hN x))).
  split; first exact: le_trans h3 (ler_wpM2r hvw (hw2 _ (hN x))).
  split; first exact: le_trans h4 (ler_wpM2r hv (hw1 _ (hN x))).
  exact: le_trans h5 (ler_wpM2r hvw (hw1 _ (hN x))).
have [a [h1 h2]] := dgpr_ibp_smooth hc hpos hg hdr hH2 hdv hE2 hsym hH2c hb.
exists a; split; last exact: h2.
have -> : (fun x => - (rho x * evR 2 [ffun _ : 'I_2 => e x] (D2h x))) =
    (fun x => - (rho x * H2 x (e x) (e x))).
  by apply: funext=> x; rewrite hH2v multilinear_successor_constant_arguments.
exact: h1.
Qed.
End Bridges.
