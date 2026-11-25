(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3;
    blueprint dgpr_blueprint.tex, proof of lem:regularity: weighted bounds
    of the higher differentials of reciprocals, logarithms and solutions of
    first order relations Dg = P (DF), by induction on the order.

    The differentials are Federer's higher differentials of 3.1.11 with
    values in the spaces of continuous multilinear maps; a weighted bound
    of order j is [dgpr_weighted_derivative] of DgprWeightedBilinear.v.
    The induction uses three facts of Federer 3.1.11: the identification of
    D^q (D f) with D^(q+1) f (p. 219), the Leibniz formula for a bilinear
    expression (p. 220, through DgprWeightedBilinear.v), and the chain rule
    3.1.1(3) for the first differential of [x |-> phi(F(x))]. If the first
    differential field of g is [x |-> P(x) DF(x)], weighted bounds of the
    differentials of P and DF of order at most k give a weighted bound of
    the differential of g of order k + 1. For g = F^(-1) one has
    P = -g^2, so that the bounds of g of order at most k give those of P;
    this is the induction of the blueprint for the derivatives of S^(-1).
    On a strip a <= t <= b of Omega_T the weights are
    [p |-> c (1 + |x|)^c phi(p)] for a fixed positive function phi. The
    last section shows that [(t,x) |-> (T - t)^(1/2)] and
    [(t,x) |-> (T - t)^(-1/2)] have derivatives of every order bounded on
    such a strip when b < T, by the same induction with
    D (T - t)^(-1/2) = 2^(-1) (T - t)^(-3/2) D t. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra ring.
From Federer Require Import Hom RealNormUP NormClassOneUP NormDifferentialUP NormDifferentialChain
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearSealed ContinuousMultilinearOne
  ContinuousMultilinearBilinearLift NormBoundedBilinearUP ContinuousMultilinearZero
  NormClassZeroBilinear NormHigherBilinearFirstField NormHigherDifferentialUP
  NormClassHigherUP NormClassHigherLaws NormClassHigherArithmetic
  NormClassHigherDerivative NormClassHigherBilinear
  NormHigherDifferentialGrouping ContinuousMultilinearGroupingFamily
  NormHigherDifferentialArithmetic NormHigherDifferentialUnique NormHigherDifferentialFirst
  NormHigherDifferentialConstant NormRegularity NormRegularityOperations NormRegularityBilinear
  ScalarNormalizationRegularity ScalarReciprocalDifferential ScalarSquareRootDifferential
  RealExponentialUP RealExponentialSealed RealExponentialLaws RealLogarithmDifferential
  NormHigherDifferentialLocal NormDifferentialLinear NormDifferentialArithmetic ContinuousOperatorUP
  RealPower RealPowerNaturalHausdorff EuclideanInnerProduct InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations ScalarInnerProduct ProductInner.
From DPGPR Require Import DgprGrowthClasses DgprWeightedBilinear DgprIdentitiesSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section FieldShift.
Variable R : realType.
Variables (X Y : lmodType R) (NX : X -> R) (NY : Y -> R).
Hypotheses (hNX : is_real_norm NX) (hNY : is_real_norm NY).
Variables (A K0 : X -> Prop).
Local Notation Z k := (@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ev k := (@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN k := (@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ k := (@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Local Notation hZ1 := (continuous_multilinear_norm_is_norm hNY (hZ 1%N)).
Local Notation W k := (@ContinuousMultilinear.space R k X (Z 1%N) NX (ZN 1%N) hNX hZ1).
Local Notation ew k := (@ContinuousMultilinear.evaluation R k X (Z 1%N) NX (ZN 1%N) hNX hZ1).
Local Notation WN k := (@ContinuousMultilinear.norm R k X (Z 1%N) NX (ZN 1%N) hNX hZ1).
Local Notation hW k := (@ContinuousMultilinear.laws R k X (Z 1%N) NX (ZN 1%N) hNX hZ1).
Local Notation HD := (has_norm_higher_differential NX (fun j => ev j) (fun j => ZN j)).
Local Notation WDY := (dgpr_weighted_derivative NX A K0 (fun j => ev j) (fun j => ZN j)).
Local Notation WDF := (dgpr_weighted_derivative NX A K0 (fun j => ew j) (fun j => WN j)).

(** Source for [dgpr_weighted_field_shift]: Federer 3.1.11, p. 219: if F
    is the field of first differentials of f on A, then D^k F(x)
    corresponds to D^(k+1) f(x) under an isometry, hence a weighted bound
    of D^k F is a weighted bound of D^(k+1) f and conversely; proof of
    lem:regularity. *)
Lemma dgpr_weighted_field_shift (f : X -> Y) (F : X -> Z 1%N) (C : (X -> R) -> Prop) (k : nat) :
  (forall a, A a -> HD A f 1 a (F a)) -> (WDF C F k <-> WDY C f k.+1).
Proof.
move=> hF.
have [J [K [hJ [hJN [hJK hKJ]]]]] :=
  continuous_multilinear_grouping_family_exists hNX hNY (fun j => hZ j) (fun j => hW j).
have hFrep x z : HD A f 1 x z -> F x = z.
  move=> hz; have hx := norm_higher_differential_domain hNX hz.
  exact: (norm_higher_differential_unique hNX hNY (fun j => hZ j) (hF x hx) hz).
have hdom := dgpr_first_differential_domain hNX hF.
split.
- move=> [w [hw hwb]]; exists w; split => // x z hx hz.
  have hgr := @norm_higher_differential_grouping R X Y NX NY hNX _ _ _ (fun j => hZ j) 1%N (fun q => W q) (fun q => ew q) (fun q => WN q)
    J K hJ hJN hJK hKJ A f F hFrep k x (J k z).
  rewrite hdom in hgr.
  have hJz := hgr.2 (ex_intro _ z (conj hz erefl)).
  rewrite -hJN; exact: hwb x _ hx hJz.
- move=> [w [hw hwb]]; exists w; split => // x y hx hy.
  have hgr := @norm_higher_differential_grouping R X Y NX NY hNX _ _ _ (fun j => hZ j) 1%N (fun q => W q) (fun q => ew q) (fun q => WN q)
    J K hJ hJN hJK hKJ A f F hFrep k x y.
  rewrite hdom in hgr.
  have [z [hz ->]] := hgr.1 hy.
  rewrite hJN; exact: hwb x z hx hz.
Qed.

(** Source for [dgpr_weighted_add]: D^k (f + g) = D^k f + D^k g (Federer
    3.1.11, p. 220) and the triangle inequality give a weighted bound for
    f + g from weighted bounds of f and g; proof of lem:regularity. *)
Lemma dgpr_weighted_add (f g : X -> Y) (C : (X -> R) -> Prop) (k : nat) :
  (forall w w', C w -> C w' -> exists w'', C w'' /\ forall x, K0 x -> w x + w' x <= w'' x) ->
  norm_class hNX hNY A f k -> norm_class hNX hNY A g k ->
  WDY C f k -> WDY C g k -> WDY C (fun x => f x + g x) k.
Proof.
move=> hC [_ [D1 [hD1 _]]] [_ [D2 [hD2 _]]] [w [hw hwb]] [w' [hw' hw'b]].
have [w'' [hw'' hle]] := hC w w' hw hw'.
exists w''; split => // x z hx hz.
have hxA := norm_higher_differential_domain hNX hz.
have hs := norm_higher_differential_field_add hNX hNY (fun j => hZ j) hD1 hD2 hxA.
rewrite (norm_higher_differential_unique hNX hNY (fun j => hZ j) hz hs).
apply: le_trans (real_seminorm_triangle (continuous_multilinear_norm_is_norm hNY (hZ k)).1 _ _) _.
apply: le_trans (hle x hx); apply: lerD.
- exact: hwb x _ hx (hD1 x hxA).
- exact: hw'b x _ hx (hD2 x hxA).
Qed.

(** Source for [dgpr_weighted_mono]: a weighted bound with a weight of a
    class C is one with a weight of a class C' when every weight of C is
    dominated on K0 by one of C'; proof of lem:regularity. *)
Lemma dgpr_weighted_mono (f : X -> Y) (C C' : (X -> R) -> Prop) (k : nat) :
  (forall w, C w -> exists w', C' w' /\ forall x, K0 x -> w x <= w' x) ->
  WDY C f k -> WDY C' f k.
Proof.
move=> hC [w [hw hwb]]; have [w' [hw' hle]] := hC w hw.
exists w'; split => // x z hx hz; exact: le_trans (hwb x z hx hz) (hle x hx).
Qed.

(** Source for [dgpr_weighted_ext]: weighted bounds transfer between
    equal maps; proof of lem:regularity. *)
Lemma dgpr_weighted_ext (f g : X -> Y) (C : (X -> R) -> Prop) (k : nat) :
  f = g -> WDY C f k -> WDY C g k.
Proof. by move=> ->. Qed.
(** Source for [dgpr_weighted_zero]: the zeroth differential of f at x
    is f(x) (Federer 3.1.11, p. 219), so a weight dominating NY(f) on K0
    gives a weighted bound of order 0; proof of lem:regularity. *)
Lemma dgpr_weighted_zero (f : X -> Y) (C : (X -> R) -> Prop) (w : X -> R) :
  C w -> (forall x, K0 x -> A x -> NY (f x) <= w x) -> WDY C f 0.
Proof.
move=> hw hb; exists w; split => // x z hx [hxA hz].
rewrite (continuous_multilinear_zero_norm hNY (hZ 0%N)) hz; exact: hb x hx hxA.
Qed.

(** Source for [dgpr_weighted_agree]: the higher differentials of f on
    the open set A depend only on the values of f on A (Federer 3.1.11,
    pp. 218-219), so weighted bounds transfer between maps agreeing on A;
    proof of lem:regularity. *)
Lemma dgpr_weighted_agree (f g : X -> Y) (C : (X -> R) -> Prop) (k : nat) :
  (forall x, A x -> norm_domain_interior NX A x) -> (forall x, A x -> f x = g x) ->
  WDY C f k -> WDY C g k.
Proof.
move=> hAo hfg [w [hw hwb]]; exists w; split => // x z hx hz.
have hxA := norm_higher_differential_domain hNX hz.
have hh := @norm_higher_differential_local_agreement R X Y NX NY hNX hNY _ _ _ (fun j => hZ j) k
  A A A f g hAo (fun x _ => iff_refl (A x)) (fun x _ hx => hfg x hx) x hxA z.
exact: hwb x z hx (hh.2 hz).
Qed.
End FieldShift.

Section ProductAllOrders.
Variable R : realType.
Variables (X : lmodType R) (NX : X -> R).
Hypothesis hNX : is_real_norm NX.
Variables (A K0 : X -> Prop).
Local Notation ST Y NY hNY := (fun j => @ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation SN Y NY hNY := (fun j => @ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation SL Y NY hNY := (fun j => @ContinuousMultilinear.laws R j X Y NX NY hNX hNY).

(** Source for [dgpr_weighted_product]: Leibniz formula of Federer
    3.1.11, p. 220, for a bounded bilinear map, with weighted bounds of all
    orders (DgprWeightedBilinear.v); proof of lem:regularity. *)
Lemma dgpr_weighted_product (U V W : lmodType R) (NU : U -> R) (NV : V -> R) (NW : W -> R)
    (hNU : is_real_norm NU) (hNV : is_real_norm NV) (hNW : is_real_norm NW)
    (B : U -> V -> W) (C1 C2 C3 : (X -> R) -> Prop) (f : X -> U) (g : X -> V) :
  norm_bounded_bilinear NU NV NW B ->
  (forall b w1 w2, 0 <= b -> C1 w1 -> C2 w2 ->
    exists w3, C3 w3 /\ forall x, K0 x -> b * (w1 x * w2 x) <= w3 x) ->
  (forall w w', C3 w -> C3 w' -> exists w'', C3 w'' /\ forall x, K0 x -> w x + w' x <= w'' x) ->
  norm_class_all_orders hNX hNU A f -> norm_class_all_orders hNX hNV A g ->
  (forall j, dgpr_weighted_derivative NX A K0 (ST U NU hNU) (SN U NU hNU) C1 f j) ->
  (forall j, dgpr_weighted_derivative NX A K0 (ST V NV hNV) (SN V NV hNV) C2 g j) ->
  forall j, dgpr_weighted_derivative NX A K0 (ST W NW hNW) (SN W NW hNW) C3 (fun x => B (f x) (g x)) j.
Proof.
move=> hB hC12 hC3 hf hg hbf hbg j.
exact: (@dgpr_bilinear_weighted_derivative R X NX hNX A K0 C1 C2 C3 hC12 hC3 j U V W NU NV NW
  hNU hNV hNW _ _ _ _ _ _ _ _ _ (SL U NU hNU) (SL V NV hNV) (SL W NW hNW) f g B hB (hf j) (hg j)
  (fun i _ => hbf i) (fun i _ => hbg i)).
Qed.
End ProductAllOrders.

Section ScalarRelations.
Variable R : realType.
Variables (X : lmodType R) (NX : X -> R).
Hypothesis hNX : is_real_norm NX.
Variables (A K0 : X -> Prop).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation Z k := (@ContinuousMultilinear.space R k X R^o NX A1 hNX hA).
Local Notation ev k := (@ContinuousMultilinear.evaluation R k X R^o NX A1 hNX hA).
Local Notation ZN k := (@ContinuousMultilinear.norm R k X R^o NX A1 hNX hA).
Local Notation hZ k := (@ContinuousMultilinear.laws R k X R^o NX A1 hNX hA).
Local Notation hZ1 := (continuous_multilinear_norm_is_norm hA (hZ 1%N)).
Local Notation W k := (@ContinuousMultilinear.space R k X (Z 1%N) NX (ZN 1%N) hNX hZ1).
Local Notation ew k := (@ContinuousMultilinear.evaluation R k X (Z 1%N) NX (ZN 1%N) hNX hZ1).
Local Notation WN k := (@ContinuousMultilinear.norm R k X (Z 1%N) NX (ZN 1%N) hNX hZ1).
Local Notation hW k := (@ContinuousMultilinear.laws R k X (Z 1%N) NX (ZN 1%N) hNX hZ1).
Local Notation HD := (has_norm_higher_differential NX (fun j => ev j) (fun j => ZN j)).
Local Notation WDY := (dgpr_weighted_derivative NX A K0 (fun j => ev j) (fun j => ZN j)).
Local Notation WDF := (dgpr_weighted_derivative NX A K0 (fun j => ew j) (fun j => WN j)).

(** Source for [dgpr_scalar_vector_bilinear]: [(s,z) |-> s z] is a
    bounded bilinear map with constant 1 (Federer 1.10.5); proof of
    lem:regularity. *)
Lemma dgpr_scalar_vector_bilinear (V : lmodType R) (NV : V -> R) (hNV : is_real_norm NV) :
  norm_bounded_bilinear A1 NV NV (fun (s : R^o) (v : V) => s *: v).
Proof.
split.
- split.
  + by move=> v a s t /=; rewrite scalerDl scalerA.
  + by move=> s a v w /=; rewrite scalerDr scalerA mulrC -scalerA.
- exists 1; split; first exact: ler01.
  by move=> s v; rewrite mul1r (real_seminorm_scale hNV.1).
Qed.

(** Source for [dgpr_scalar_mul_bilinear]: multiplication of reals is a
    bounded bilinear map with constant 1; proof of lem:regularity. *)
Lemma dgpr_scalar_mul_bilinear :
  norm_bounded_bilinear A1 A1 A1 (fun s t : R^o => s * t : R^o).
Proof.
split.
- split.
  + by move=> v a s t /=; change ((a * s + t) * v = a * (s * v) + t * v); ring.
  + by move=> s a v w /=; change (s * (a * v + w) = a * (s * v) + s * w); ring.
- exists 1; split; first exact: ler01.
  by move=> s t; rewrite mul1r normrM.
Qed.

(** Source for [dgpr_scalar_product_bilinear]: [(s,t) |-> c s t] is a
    bounded bilinear map on R with constant |c|; proof of
    lem:regularity. *)
Lemma dgpr_scalar_product_bilinear (c : R) :
  norm_bounded_bilinear A1 A1 A1 (fun s t : R^o => c * (s * t) : R^o).
Proof.
split.
- split.
  + by move=> v a s t /=; change (c * ((a * s + t) * v) = a * (c * (s * v)) + c * (t * v)); ring.
  + by move=> s a v w /=; change (c * (s * (a * v + w)) = a * (c * (s * v)) + c * (s * w)); ring.
- exists `|c|; split; first exact: normr_ge0.
  by move=> s t; rewrite !normrM.
Qed.

(** Source for [dgpr_first_field_compose]: the chain rule of Federer
    3.1.1(3), p. 210: if F has the first differential z at a and phi has
    the derivative c at F(a), then [x |-> phi(F(x))] has the first
    differential c z at a (Federer 3.1.11, pp. 218-219, for the order 1);
    proof of lem:regularity. *)
Lemma dgpr_first_field_compose (F : X -> R^o) (Dom : R^o -> Prop) (phi : R^o -> R^o)
    (M : Hom R^o R^o) (c : R) (a : X) (z : Z 1%N) :
  (forall x, A x -> Dom (F x)) -> HD A F 1 a z ->
  has_norm_differential A1 A1 Dom phi (F a) M -> (forall s, M s = s * c) ->
  HD A (fun x => phi (F x)) 1 a (c *: z).
Proof.
move=> hdom hF hphi hM.
have hL := (norm_higher_differential_first hNX hA (fun j => hZ j) A F a z).1 hF.
have hc := norm_differential_chain hNX hA hA hL hphi.
have e : (fun x => A x /\ Dom (F x)) = A.
  by apply: funext => x; apply: propext; split => [[]|hx] //; split => //; exact: hdom.
rewrite e in hc.
apply/(norm_higher_differential_first hNX hA (fun j => hZ j) A (fun x => phi (F x)) a (c *: z)).
suff -> : continuous_multilinear_one_operator (hZ 1%N) (c *: z) =
  hom_comp M (continuous_multilinear_one_operator (hZ 1%N) z) by [].
apply: hom_ext => v; rewrite hom_compE hM.
change (ev 1%N [ffun i => v] (c *: z) = ev 1%N [ffun i => v] z * c).
by rewrite linearZ /= mulrC.
Qed.

Variables (CG CP C1 : (X -> R) -> Prop).
Hypothesis hPC1 : forall b w1 w2, 0 <= b -> CP w1 -> C1 w2 ->
  exists w3, CG w3 /\ forall x, K0 x -> b * (w1 x * w2 x) <= w3 x.
Hypothesis hCG : forall w w', CG w -> CG w' ->
  exists w'', CG w'' /\ forall x, K0 x -> w x + w' x <= w'' x.

(** Source for [dgpr_weighted_relation]: if the first differential field
    of g on A is [x |-> P(x) F1(x)], the bounds of D^i P (weights of CP)
    for i <= k follow from those of D^i g (weights of CG) for i <= k, and
    the derivatives of F1 have bounds with weights of C1, then all
    derivatives of g have bounds with weights of CG. Induction on the
    order with the Leibniz formula and the identification of D^k D g with
    D^(k+1) g (Federer 3.1.11, pp. 219-220); proof of lem:regularity. *)
Theorem dgpr_weighted_relation (G P : X -> R^o) (F1 : X -> Z 1%N) :
  norm_class_all_orders hNX hA A P ->
  (forall k, norm_class_higher NX (ZN 1%N) (fun j => ew j) (fun j => WN j) A F1 k) ->
  (forall a, A a -> HD A G 1 a (P a *: F1 a)) ->
  (forall i, WDF C1 F1 i) ->
  (forall k, (forall i, (i <= k)%N -> WDY CG G i) -> forall i, (i <= k)%N -> WDY CP P i) ->
  WDY CG G 0 ->
  forall j, WDY CG G j.
Proof.
move=> hP hF1 hfield hb1 hstep h0.
move=> m; assert (hall : forall k i, (i <= k)%N -> WDY CG G i); last first.
  exact (hall m m (leqnn m)).
elim=> [|k ih] i hi.
  by have -> : i = 0%N by apply/eqP; rewrite -leqn0.
case: (ltngtP i k.+1) hi => [hlt _|//|-> _]; first exact: ih i hlt.
have hPk := hstep k ih.
have hG1 : WDF CG (fun x => P x *: F1 x) k.
  exact: (@dgpr_bilinear_weighted_derivative R X NX hNX A K0 CP C1 CG hPC1 hCG k
    R^o (Z 1%N) (Z 1%N) A1 (ZN 1%N) (ZN 1%N) hA hZ1 hZ1 _ _ _ _ _ _ _ _ _
    (fun j => hZ j) (fun j => hW j) (fun j => hW j) P F1 (fun s z => s *: z)
    (dgpr_scalar_vector_bilinear hZ1) (hP k) (hF1 k) hPk (fun i _ => hb1 i)).
exact: (dgpr_weighted_field_shift K0 CG k hfield).1 hG1.
Qed.
End ScalarRelations.

Section ScalarRelationApplications.
Variable R : realType.
Variables (X : lmodType R) (NX : X -> R).
Hypothesis hNX : is_real_norm NX.
Variables (A K0 : X -> Prop).
Hypothesis hAo : forall x, A x -> norm_domain_interior NX A x.
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation LOG := (@RealExponential.logarithm R).
Local Notation Z k := (@ContinuousMultilinear.space R k X R^o NX A1 hNX hA).
Local Notation ev k := (@ContinuousMultilinear.evaluation R k X R^o NX A1 hNX hA).
Local Notation ZN k := (@ContinuousMultilinear.norm R k X R^o NX A1 hNX hA).
Local Notation hZ k := (@ContinuousMultilinear.laws R k X R^o NX A1 hNX hA).
Local Notation hZ1 := (continuous_multilinear_norm_is_norm hA (hZ 1%N)).
Local Notation W k := (@ContinuousMultilinear.space R k X (Z 1%N) NX (ZN 1%N) hNX hZ1).
Local Notation ew k := (@ContinuousMultilinear.evaluation R k X (Z 1%N) NX (ZN 1%N) hNX hZ1).
Local Notation WN k := (@ContinuousMultilinear.norm R k X (Z 1%N) NX (ZN 1%N) hNX hZ1).
Local Notation hW k := (@ContinuousMultilinear.laws R k X (Z 1%N) NX (ZN 1%N) hNX hZ1).
Local Notation HD := (has_norm_higher_differential NX (fun j => ev j) (fun j => ZN j)).
Local Notation WDY := (dgpr_weighted_derivative NX A K0 (fun j => ev j) (fun j => ZN j)).
Local Notation WDF := (dgpr_weighted_derivative NX A K0 (fun j => ew j) (fun j => WN j)).

(** Source for [dgpr_weighted_constant]: a constant map has the zeroth
    differential c and vanishing differentials of positive order (Federer
    3.1.11, p. 221); its derivatives have weighted bounds by any weight
    dominating NV(c); proof of lem:regularity. *)
Lemma dgpr_weighted_constant (V : lmodType R) (NV : V -> R) (hNV : is_real_norm NV) (c : V)
    (C : (X -> R) -> Prop) (w : X -> R) :
  C w -> (forall x, K0 x -> 0 <= w x /\ NV c <= w x) ->
  forall j, dgpr_weighted_derivative NX A K0
    (fun k => @ContinuousMultilinear.evaluation R k X V NX NV hNX hNV)
    (fun k => @ContinuousMultilinear.norm R k X V NX NV hNX hNV) C (fun _ => c) j.
Proof.
move=> hw hwb j; exists w; split => // x z hx hz.
have hZV k := @ContinuousMultilinear.laws R k X V NX NV hNX hNV.
have [c0 hc0] := continuous_multilinear_zero_surjective hNV (hZV 0%N) c.
have hxA := norm_higher_differential_domain hNX hz.
have hcst := norm_higher_differential_constant hNX hNV hZV hAo hc0 j hxA.
rewrite (norm_higher_differential_unique hNX hNV hZV hz hcst).
have [hw0 hwc] := hwb x hx.
clear hz hcst; move: z => _.
case: j => [|j] /=.
- by rewrite (continuous_multilinear_zero_norm hNV (hZV 0%N)) hc0.
- by rewrite (real_seminorm_zero (continuous_multilinear_norm_is_norm hNV (hZV j.+1)).1).
Qed.

Variables (Cp Cm1 Cm2 : (X -> R) -> Prop).
Hypothesis h11 : forall b w1 w2, 0 <= b -> Cm1 w1 -> Cm1 w2 ->
  exists w3, Cm2 w3 /\ forall x, K0 x -> b * (w1 x * w2 x) <= w3 x.
Hypothesis h21 : forall b w1 w2, 0 <= b -> Cm2 w1 -> Cp w2 ->
  exists w3, Cm1 w3 /\ forall x, K0 x -> b * (w1 x * w2 x) <= w3 x.
Hypothesis hs1 : forall w w', Cm1 w -> Cm1 w' ->
  exists w'', Cm1 w'' /\ forall x, K0 x -> w x + w' x <= w'' x.
Hypothesis hs2 : forall w w', Cm2 w -> Cm2 w' ->
  exists w'', Cm2 w'' /\ forall x, K0 x -> w x + w' x <= w'' x.

(** Source for [dgpr_first_field_exists]: a map of class 1 on A has a
    field of first differentials on A, which is of class k when the map
    is of class k + 1 (Federer 3.1.11, pp. 219-221); proof of
    lem:regularity. *)
Lemma dgpr_first_field_exists (F : X -> R^o) :
  norm_class_all_orders hNX hA A F ->
  exists F1 : X -> Z 1%N, (forall a, A a -> HD A F 1 a (F1 a)) /\
    forall k, norm_class_higher NX (ZN 1%N) (fun j => ew j) (fun j => WN j) A F1 k.
Proof.
move=> hF; have [_ [F1 [hF1 _]]] := hF 1%N.
exists F1; split => // k.
exact: (@norm_class_higher_derivative_field R 1%N k X R^o NX A1 hNX hA _ _ _ (fun j => hZ j)
  (fun j => W j) (fun j => ew j) (fun j => WN j) (fun j => hW j) A F F1 (hF (1 + k)%N) hF1).
Qed.

(** Source for [dgpr_weighted_reciprocal]: blueprint lem:regularity,
    proof: if F does not vanish on A, is of class infinity, and its
    derivatives have weighted bounds of the class Cp, then the derivatives
    of F^(-1) have weighted bounds of the class Cm1, provided |F^(-1)| has
    one and products of weights behave like products of the powers
    F^(-1) F^(-1) = F^(-2) and F^(-2) F = F^(-1). The first differential
    of F^(-1) is -F^(-2) DF (Federer 3.1.1, p. 209, and 3.1.11, p. 223). *)
Theorem dgpr_weighted_reciprocal (F : X -> R^o) :
  (forall x, A x -> F x != 0) -> norm_class_all_orders hNX hA A F ->
  (forall j, WDY Cp F j) -> WDY Cm1 (fun x => (F x)^-1) 0 ->
  forall j, WDY Cm1 (fun x => (F x)^-1) j.
Proof.
move=> hF0 hF hb hb0.
pose G x : R^o := (F x)^-1.
have hG : norm_class_all_orders hNX hA A G.
  move=> k; exact: (norm_class_compose_on hF0 (hF k) (scalar_reciprocal_norm_class R k)).
have [F1 [hF1 hF1c]] := dgpr_first_field_exists hF.
have hb1 i : WDF Cp F1 i by exact: (dgpr_weighted_field_shift K0 Cp i hF1).2 (hb i.+1).
pose P x : R^o := (-1) * (G x * G x).
have hP : norm_class_all_orders hNX hA A P.
  move=> k; have h := norm_class_scale (-1) (norm_class_scalar_product (hG k) (hG k)).
  by apply: (norm_class_domain_agreement _ h) => x _.
have hfield a : A a -> HD A G 1 a (P a *: F1 a).
  move=> ha.
  apply: (dgpr_first_field_compose (Dom := fun t => t != 0) hF0 (hF1 a ha)
    (scalar_reciprocal_differential (hF0 a ha))) => s.
  change (s * - ((F a)^-1 ^+ 2) = s * ((-1) * ((F a)^-1 * (F a)^-1))).
  by rewrite expr2 mulN1r.
have hstep k : (forall i, (i <= k)%N -> WDY Cm1 G i) -> forall i, (i <= k)%N -> WDY Cm2 P i.
  move=> hk i hi.
  exact: (@dgpr_bilinear_weighted_derivative R X NX hNX A K0 Cm1 Cm1 Cm2 h11 hs2 i
    R^o R^o R^o A1 A1 A1 hA hA hA _ _ _ _ _ _ _ _ _ (fun j => hZ j) (fun j => hZ j) (fun j => hZ j)
    G G (fun s t : R^o => (-1) * (s * t) : R^o) (dgpr_scalar_product_bilinear (-1))
    (hG i) (hG i) (fun i' hi' => hk i' (leq_trans hi' hi)) (fun i' hi' => hk i' (leq_trans hi' hi))).
exact: (dgpr_weighted_relation h21 hs1 hP hF1c hfield hb1 hstep hb0).
Qed.

Variable C0 : (X -> R) -> Prop.
Hypothesis h10 : forall b w1 w2, 0 <= b -> Cm1 w1 -> Cp w2 ->
  exists w3, C0 w3 /\ forall x, K0 x -> b * (w1 x * w2 x) <= w3 x.
Hypothesis hs0 : forall w w', C0 w -> C0 w' ->
  exists w'', C0 w'' /\ forall x, K0 x -> w x + w' x <= w'' x.

(** Source for [dgpr_weighted_logarithm]: blueprint lem:regularity,
    proof: D log F = F^(-1) DF (Federer 3.1.1, p. 209), so weighted bounds
    of the derivatives of F (class Cp) and F^(-1) (class Cm1) give
    weighted bounds of the derivatives of log F of positive order (class
    C0); the bound of order 0 is a hypothesis. *)
Theorem dgpr_weighted_logarithm (F : X -> R^o) :
  (forall x, A x -> 0 < F x) -> norm_class_all_orders hNX hA A F ->
  (forall j, WDY Cp F j) -> (forall j, WDY Cm1 (fun x => (F x)^-1) j) ->
  WDY C0 (fun x => LOG (F x)) 0 ->
  forall j, WDY C0 (fun x => LOG (F x)) j.
Proof.
move=> hF0 hF hb hbm hb0.
have [F1 [hF1 hF1c]] := dgpr_first_field_exists hF.
have hb1 i : WDF Cp F1 i by exact: (dgpr_weighted_field_shift K0 Cp i hF1).2 (hb i.+1).
have hP : norm_class_all_orders hNX hA A (fun x => (F x)^-1).
  move=> k; apply: (norm_class_compose_on _ (hF k) (scalar_reciprocal_norm_class R k)).
  by move=> x hx; rewrite gt_eqF // hF0.
have hfield a : A a -> HD A (fun x => LOG (F x)) 1 a ((F a)^-1 *: F1 a).
  move=> ha.
  apply: (dgpr_first_field_compose (Dom := setT) _ (hF1 a ha)
    (real_logarithm_differential (hF0 a ha))) => // s.
  by change ((F a)^-1 * s = s * (F a)^-1); rewrite mulrC.
exact: (dgpr_weighted_relation h10 hs0 hP hF1c hfield hb1 (fun k _ i _ => hbm i) hb0).
Qed.
End ScalarRelationApplications.

Section RelativeWeights.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation E := (@RealExponential.exponential R).
Local Notation L := (@RealExponential.logarithm R).
Local Notation hE := (@RealExponential.laws R).
Variables a b : R.
Local Notation K0 := (dgpr_time_strip a b).

(** Source for [dgpr_relative_class]: the weights w with
    0 <= w(t,x) <= c (1 + |x|)^c phi(t,x) for a <= t <= b, for some
    0 < c, relative to a fixed function phi; the bounds (eq:reg:ratio) of
    the proof of lem:regularity are bounds by such weights with phi = S
    and phi = rho. *)
Definition dgpr_relative_class (phi : TX -> R) (w : TX -> R) : Prop :=
  exists c, 0 < c /\ forall p, K0 p -> 0 <= w p /\ w p <= dgpr_polynomial_weight c (N p.2) * phi p.

Let hr (p : TX) : 0 <= N p.2 := inner_norm_nonnegative (@euclidean_inner_productP R n) p.2.

(** Source for [dgpr_relative_product]: c1 (1+r)^c1 phi1 times
    c2 (1+r)^c2 phi2 is at most c3 (1+r)^c3 phi3 when phi1 phi2 <= phi3;
    proof of lem:regularity. *)
Lemma dgpr_relative_product (phi1 phi2 phi3 : TX -> R) :
  (forall p, K0 p -> [/\ 0 <= phi1 p, 0 <= phi2 p & phi1 p * phi2 p <= phi3 p]) ->
  forall bb w1 w2, 0 <= bb -> dgpr_relative_class phi1 w1 -> dgpr_relative_class phi2 w2 ->
    exists w3, dgpr_relative_class phi3 w3 /\ forall p, K0 p -> bb * (w1 p * w2 p) <= w3 p.
Proof.
move=> hphi bb w1 w2 hb [c1 [hc1 h1]] [c2 [hc2 h2]].
have hc3 : 0 < bb * c1 * c2 + c1 + c2.
  by have := mulr_ge0 (mulr_ge0 hb (ltW hc1)) (ltW hc2); lra.
exists (fun p => dgpr_polynomial_weight (bb * c1 * c2 + c1 + c2) (N p.2) * phi3 p); split.
  exists (bb * c1 * c2 + c1 + c2); split => // p hp; split => //.
  have [h10 h20 h12] := hphi p hp.
  exact: mulr_ge0 (dgpr_polynomial_weight_nonnegative _ (ltW hc3)) (le_trans (mulr_ge0 h10 h20) h12).
move=> p hp; have [h10 h20 h12] := hphi p hp.
have [hw1 hw1'] := h1 p hp; have [hw2 hw2'] := h2 p hp.
have hP1 := dgpr_polynomial_weight_nonnegative (N p.2) (ltW hc1).
have hP2 := dgpr_polynomial_weight_nonnegative (N p.2) (ltW hc2).
have hprod := dgpr_polynomial_weight_product hb hc1 hc2 (hr p).
apply: le_trans (ler_wpM2l hb (ler_pM hw1 hw2 hw1' hw2')) _.
have -> : bb * (dgpr_polynomial_weight c1 (N p.2) * phi1 p * (dgpr_polynomial_weight c2 (N p.2) * phi2 p)) =
  (bb * (dgpr_polynomial_weight c1 (N p.2) * dgpr_polynomial_weight c2 (N p.2))) * (phi1 p * phi2 p) by ring.
exact: ler_pM (mulr_ge0 hb (mulr_ge0 hP1 hP2)) (mulr_ge0 h10 h20) hprod h12.
Qed.

(** Source for [dgpr_relative_sum]: sums of weights of the class relative
    to phi are dominated by such weights; proof of lem:regularity. *)
Lemma dgpr_relative_sum (phi : TX -> R) : (forall p, K0 p -> 0 <= phi p) ->
  forall w w', dgpr_relative_class phi w -> dgpr_relative_class phi w' ->
    exists w'', dgpr_relative_class phi w'' /\ forall p, K0 p -> w p + w' p <= w'' p.
Proof.
move=> hphi w w' [c1 [hc1 h1]] [c2 [hc2 h2]].
have hc : 0 < c1 + c2 by lra.
exists (fun p => dgpr_polynomial_weight (c1 + c2) (N p.2) * phi p); split.
  exists (c1 + c2); split => // p hp; split => //.
  exact: mulr_ge0 (dgpr_polynomial_weight_nonnegative _ (ltW hc)) (hphi p hp).
move=> p hp; have [_ hw1] := h1 p hp; have [_ hw2] := h2 p hp.
apply: le_trans (lerD hw1 hw2) _; rewrite -mulrDl.
apply: ler_wpM2r; first exact: hphi p hp.
exact: dgpr_polynomial_weight_sum hc1 hc2 (hr p).
Qed.

(** Source for [dgpr_relative_sub]: if phi <= M psi on the strip, then a
    weight relative to phi is a weight relative to psi; proof of
    lem:regularity. *)
Lemma dgpr_relative_sub (phi psi : TX -> R) (M : R) : 0 <= M ->
  (forall p, K0 p -> 0 <= psi p /\ phi p <= M * psi p) ->
  forall w, dgpr_relative_class phi w -> dgpr_relative_class psi w.
Proof.
move=> hM hphi w [c [hc h]].
have hc' : 0 < M * c * 1 + c + 1 by have := mulr_ge0 hM (ltW hc); lra.
exists (M * c * 1 + c + 1); split => // p hp.
have [hw0 hw] := h p hp; split => //.
have [hpsi hle] := hphi p hp.
have hP := dgpr_polynomial_weight_nonnegative (N p.2) (ltW hc).
have hP1 : 1 <= dgpr_polynomial_weight 1 (N p.2) := dgpr_polynomial_weight_one ler01 (hr p).
have hprod := dgpr_polynomial_weight_product hM hc ltr01 (hr p).
apply: le_trans hw _; apply: le_trans (ler_wpM2l hP hle) _.
rewrite mulrA; apply: ler_wpM2r; first exact: hpsi.
apply: le_trans hprod; rewrite mulrC; apply: ler_wpM2l; first exact: hM.
by rewrite -{1}(mulr1 (dgpr_polynomial_weight c (N p.2))); apply: ler_wpM2l; [exact: hP | exact: hP1].
Qed.

(** Source for [dgpr_relative_dominate]: the class relative to phi is
    dominated by the class relative to psi under the hypotheses of
    [dgpr_relative_sub], in the form used by [dgpr_weighted_mono]; proof
    of lem:regularity. *)
Lemma dgpr_relative_dominate (phi psi : TX -> R) (M : R) : 0 <= M ->
  (forall p, K0 p -> 0 <= psi p /\ phi p <= M * psi p) ->
  forall w, dgpr_relative_class phi w ->
    exists w', dgpr_relative_class psi w' /\ forall p, K0 p -> w p <= w' p.
Proof.
by move=> hM hphi w hw; exists w; split => //; exact: (dgpr_relative_sub hM hphi).
Qed.

(** Source for [dgpr_polynomial_power_le]: c (1 + r)^K <= c' (1 + r)^c'
    with c' = c + K, since 1 + r >= 1 (Federer 2.4.12, p. 86, real
    powers); proof of lem:regularity. *)
Lemma dgpr_polynomial_power_le (c r : R) (K : nat) : 0 < c -> 0 <= r ->
  c * (1 + r) ^+ K <= dgpr_polynomial_weight (c + K%:R) r.
Proof.
move=> hc hr0; rewrite dgpr_polynomial_weightE //.
have h1 : 0 < 1 + r by lra.
rewrite -(real_power_natural_exponent K (ltW h1)) real_power_positive_base //.
have hL := dgpr_log_one_plus_nonnegative hr0.
apply: ler_pM.
- exact: ltW.
- exact: ltW (dgpr_exponential_positive _).
- by rewrite lerDl.
- rewrite real_exponential_order; apply: ler_wpM2r; first exact: hL.
  by rewrite lerDr; exact: ltW.
Qed.

(** Source for [dgpr_relative_joint]: a bound
    ||D^j F(t,x)|| <= c (1 + |x|)^K h(t,x) on the strip with
    0 <= h <= M phi, as given by the joint bounds of DgprBackwardHeatDecay.v,
    is a bound by a weight relative to phi; proof of lem:regularity. *)
Lemma dgpr_relative_joint (phi h : TX -> R) (M c : R) (K : nat) :
  0 <= M -> 0 < c -> (forall p, K0 p -> [/\ 0 <= phi p, 0 <= h p & h p <= M * phi p]) ->
  exists w, dgpr_relative_class phi w /\ forall p, K0 p -> c * (1 + N p.2) ^+ K * h p <= w p.
Proof.
move=> hM hc hphi.
have hcK : 0 < c + K%:R by rewrite ltr_wpDr.
have hc' : 0 < M * (c + K%:R) * 1 + (c + K%:R) + 1 by have := mulr_ge0 hM (ltW hcK); lra.
exists (fun p => dgpr_polynomial_weight (M * (c + K%:R) * 1 + (c + K%:R) + 1) (N p.2) * phi p); split.
  exists (M * (c + K%:R) * 1 + (c + K%:R) + 1); split => // p hp; split => //.
  have [hp0 _ _] := hphi p hp.
  exact: mulr_ge0 (dgpr_polynomial_weight_nonnegative _ (ltW hc')) hp0.
move=> p hp; have [hp0 hh0 hh] := hphi p hp.
have hpow := dgpr_polynomial_power_le K hc (hr p).
have hP := dgpr_polynomial_weight_nonnegative (N p.2) (ltW hcK).
have hP1 : 1 <= dgpr_polynomial_weight 1 (N p.2) := dgpr_polynomial_weight_one ler01 (hr p).
have hprod := dgpr_polynomial_weight_product hM hcK ltr01 (hr p).
apply: le_trans (ler_wpM2r hh0 hpow) _.
apply: le_trans (ler_wpM2l hP hh) _.
rewrite mulrA; apply: ler_wpM2r; first exact: hp0.
apply: le_trans hprod; rewrite mulrC; apply: ler_wpM2l; first exact: hM.
by rewrite -{1}(mulr1 (dgpr_polynomial_weight (c + K%:R) (N p.2))); apply: ler_wpM2l; [exact: hP | exact: hP1].
Qed.

(** Source for [dgpr_relative_polynomial]: a weight relative to the
    constant 1 is dominated by c (1 + |x|)^c, the weight of def:classes;
    proof of lem:regularity. *)
Lemma dgpr_relative_polynomial (w : TX -> R) : dgpr_relative_class (fun _ => 1) w ->
  exists c, 0 < c /\ forall p, K0 p -> w p <= dgpr_polynomial_weight c (N p.2).
Proof.
move=> [c [hc h]]; exists c; split => // p hp.
by have [_ hw] := h p hp; rewrite mulr1 in hw.
Qed.

(** Source for [dgpr_relative_gaussian]: a weight relative to phi, where
    phi <= c0 exp(-|x|^2/c0) on the strip, is dominated by a Gaussian
    weight (proof of lem:classes, the inequality
    (1 + |x|)^c exp(-|x|^2/c') <= c'' exp(-|x|^2/c'')); proof of
    lem:regularity. *)
Lemma dgpr_relative_gaussian (phi w : TX -> R) (c0 : R) : 0 < c0 ->
  (forall p, K0 p -> phi p <= dgpr_gaussian_weight c0 (N p.2)) ->
  dgpr_relative_class phi w ->
  exists c, 0 < c /\ forall p, K0 p -> w p <= dgpr_gaussian_weight c (N p.2).
Proof.
move=> hc0 hphi [c [hc h]].
exists (dgpr_polynomial_gaussian_constant 1 c c0); split.
  exact: dgpr_polynomial_gaussian_constant_positive ler01 hc hc0.
move=> p hp; have [_ hw] := h p hp.
have hP := dgpr_polynomial_weight_nonnegative (N p.2) (ltW hc).
apply: le_trans hw _; apply: le_trans (ler_wpM2l hP (hphi p hp)) _.
have h1 := dgpr_polynomial_gaussian_weight_product ler01 hc hc0 (hr p).
by rewrite mul1r in h1.
Qed.

(** Source for [dgpr_relative_weight]: the weight c (1 + |x|)^c phi
    belongs to the class relative to phi when phi >= 0 on the strip;
    proof of lem:regularity. *)
Lemma dgpr_relative_weight (phi : TX -> R) (c : R) : 0 < c -> (forall p, K0 p -> 0 <= phi p) ->
  dgpr_relative_class phi (fun p => dgpr_polynomial_weight c (N p.2) * phi p).
Proof.
move=> hc hphi; exists c; split => // p hp; split => //.
exact: mulr_ge0 (dgpr_polynomial_weight_nonnegative _ (ltW hc)) (hphi p hp).
Qed.

(** Source for [dgpr_relative_self]: for phi > 0 on the strip, phi itself
    is dominated by the weight (1 + |x|) phi of the class relative to
    phi; proof of lem:regularity. *)
Lemma dgpr_relative_self (phi : TX -> R) : (forall p, K0 p -> 0 <= phi p) ->
  exists w, dgpr_relative_class phi w /\ forall p, K0 p -> phi p <= w p.
Proof.
move=> hphi; exists (fun p => dgpr_polynomial_weight 1 (N p.2) * phi p); split.
  exact: dgpr_relative_weight ltr01 hphi.
move=> p hp; have hP1 : 1 <= dgpr_polynomial_weight 1 (N p.2) := dgpr_polynomial_weight_one ler01 (hr p).
rewrite -{1}(mul1r (phi p)); apply: ler_wpM2r; [exact: hphi p hp | exact: hP1].
Qed.
End RelativeWeights.

Section TimeFactors.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BT := (product_inner_productP (scalar_inner_productP R) (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Variables T a b : R.
Hypothesis hbT : b < T.
Local Notation OmT := (dgpr_before T).
Local Notation K0 := (dgpr_time_strip a b).
Local Notation Z k := (@ContinuousMultilinear.space R k TX R^o NT A1 hNT hA).
Local Notation ev k := (@ContinuousMultilinear.evaluation R k TX R^o NT A1 hNT hA).
Local Notation ZN k := (@ContinuousMultilinear.norm R k TX R^o NT A1 hNT hA).
Local Notation hZ k := (@ContinuousMultilinear.laws R k TX R^o NT A1 hNT hA).
Local Notation hZ1 := (continuous_multilinear_norm_is_norm hA (hZ 1%N)).
Local Notation W k := (@ContinuousMultilinear.space R k TX (Z 1%N) NT (ZN 1%N) hNT hZ1).
Local Notation ew k := (@ContinuousMultilinear.evaluation R k TX (Z 1%N) NT (ZN 1%N) hNT hZ1).
Local Notation WN k := (@ContinuousMultilinear.norm R k TX (Z 1%N) NT (ZN 1%N) hNT hZ1).
Local Notation hW k := (@ContinuousMultilinear.laws R k TX (Z 1%N) NT (ZN 1%N) hNT hZ1).
Local Notation HD := (has_norm_higher_differential NT (fun j => ev j) (fun j => ZN j)).
Local Notation WDY := (dgpr_weighted_derivative NT OmT K0 (fun j => ev j) (fun j => ZN j)).
Local Notation WDF := (dgpr_weighted_derivative NT OmT K0 (fun j => ew j) (fun j => WN j)).
Local Notation C1 := (dgpr_relative_class a b (fun _ : TX => 1)).
Local Notation rt := (fun p : TX => Num.sqrt (T - p.1) : R^o).
Local Notation irt := (fun p : TX => (Num.sqrt (T - p.1))^-1 : R^o).

Let hAo (p : TX) : OmT p -> norm_domain_interior NT OmT p := @dgpr_before_open R n T p.

(** Source for [dgpr_strip_before]: a strip a <= t <= b with b < T lies
    in Omega_T (def:classes); supporting lem:regularity. *)
Lemma dgpr_strip_before (p : TX) : K0 p -> OmT p.
Proof. by move=> /andP [_ hpb]; change (p.1 < T); exact: le_lt_trans hpb hbT. Qed.

(** Source for [dgpr_one_product]: products of weights relative to 1 are
    dominated by weights relative to 1; proof of lem:regularity. *)
Lemma dgpr_one_product : forall bb w1 w2, 0 <= bb -> C1 w1 -> C1 w2 ->
  exists w3, C1 w3 /\ forall p, K0 p -> bb * (w1 p * w2 p) <= w3 p.
Proof. by apply: dgpr_relative_product => p _; split; rewrite ?mulr1 ?ler01. Qed.

(** Source for [dgpr_one_sum]: sums of weights relative to 1 are
    dominated by weights relative to 1; proof of lem:regularity. *)
Lemma dgpr_one_sum : forall w w', C1 w -> C1 w' ->
  exists w'', C1 w'' /\ forall p, K0 p -> w p + w' p <= w'' p.
Proof. by apply: dgpr_relative_sum => p _; exact: ler01. Qed.

(** Source for [dgpr_time_first]: the affine map [(t,x) |-> T - t] has a
    constant first differential on Omega_T, the element of the space of
    continuous 1 linear maps representing [(t,x) |-> -t] (Federer 3.1.1,
    p. 210, and 3.1.11, p. 219); proof of lem:regularity. *)
Lemma dgpr_time_first : exists z0 : Z 1%N, forall p, OmT p -> HD OmT (fun q : TX => T - q.1 : R^o) 1 p z0.
Proof.
have hL := dgpr_time_negation_bounded R n.
have hop := continuous_multilinear_one_operator_space (hZ 1%N).
have [z hz] := continuous_operator_surjective hop hL.
change (continuous_multilinear_one_operator (hZ 1%N) z = dgpr_time_negation_hom R n) in hz.
exists z => p hp.
apply/(norm_higher_differential_first hNT hA (fun j => hZ j) OmT (fun q : TX => T - q.1 : R^o) p z).
rewrite hz.
have hd := norm_differential_add hA (norm_differential_linear hNT hA (hAo hp) hL)
  (norm_differential_constant hNT hA (T : R^o) (hAo hp)).
rewrite addr0 in hd.
have e : (fun x : TX => dgpr_time_negation_hom R n x + (T : R^o)) = (fun q : TX => T - q.1 : R^o).
  by apply: funext => q; change (- q.1 + T = T - q.1); rewrite addrC.
by rewrite e in hd.
Qed.

(** Source for [dgpr_time_constant_field]: a constant field of first
    differentials has weighted bounds of every order relative to 1
    (Federer 3.1.11, p. 221); proof of lem:regularity. *)
Lemma dgpr_time_constant_field (z : Z 1%N) (j : nat) : WDF C1 (fun _ => z) j.
Proof.
have hz0 := real_seminorm_nonnegative hZ1.1 z.
have hc : 0 < ZN 1%N z + 1 by rewrite ltr_wpDl.
apply: (dgpr_weighted_constant hNT hAo hZ1 (w := fun p => dgpr_polynomial_weight (ZN 1%N z + 1) (N p.2) * 1)).
  exact: dgpr_relative_weight hc (fun _ _ => ler01).
move=> p hp; rewrite mulr1; split; first exact: dgpr_polynomial_weight_nonnegative _ (ltW hc).
apply: le_trans (dgpr_polynomial_weight_one (ltW hc) (inner_norm_nonnegative _ _)).
by rewrite lerDl.
Qed.

(** Source for [dgpr_time_root_class]: [(t,x) |-> (T - t)^(1/2)] and
    [(t,x) |-> (T - t)^(-1/2)] are of class infinity on Omega_T (Federer
    3.1.11, chain rule, and 3.1.24); proof of lem:regularity. *)
Lemma dgpr_time_root_class :
  norm_class_all_orders hNT hA OmT rt /\ norm_class_all_orders hNT hA OmT irt.
Proof.
split => k; first exact: (@dgpr_sqrt_time_to_go_class R n T k).
apply: (norm_class_compose_on _ (@dgpr_sqrt_time_to_go_class R n T k) (scalar_reciprocal_norm_class R k)).
by move=> p hp; rewrite gt_eqF // sqrtr_gt0 subr_gt0.
Qed.

(** Source for [dgpr_time_root_field]: the first differential of
    [(t,x) |-> (T - t)^(1/2)] is (2 (T - t)^(1/2))^(-1) times that of
    [(t,x) |-> T - t] (Federer 3.1.1(3) and 3.1.24); proof of
    lem:regularity. *)
Lemma dgpr_time_root_field (z0 : Z 1%N) :
  (forall p, OmT p -> HD OmT (fun q : TX => T - q.1 : R^o) 1 p z0) ->
  forall p, OmT p -> HD OmT rt 1 p ((2 * Num.sqrt (T - p.1))^-1 *: z0).
Proof.
move=> hz0 p hp; have hpos : 0 < T - p.1 by rewrite subr_gt0.
apply: (dgpr_first_field_compose (Dom := fun t : R^o => 0 < t) (F := fun q : TX => T - q.1 : R^o) _
  (hz0 p hp) (scalar_square_root_differential hpos)) => [q hq|s] //.
by rewrite subr_gt0.
Qed.

(** Source for [dgpr_time_inverse_root_field]: the first differential of
    g = (T - t)^(-1/2) is g^3 times -(1/2) times that of
    [(t,x) |-> T - t] (Federer 3.1.1(3), p. 210); proof of
    lem:regularity. *)
Lemma dgpr_time_inverse_root_field (z0 : Z 1%N) :
  (forall p, OmT p -> HD OmT (fun q : TX => T - q.1 : R^o) 1 p z0) ->
  forall p, OmT p -> HD OmT irt 1 p ((irt p * (irt p * irt p)) *: ((- 2^-1) *: z0)).
Proof.
move=> hz0 p hp; have hpos : 0 < T - p.1 by rewrite subr_gt0.
have hsq : Num.sqrt (T - p.1) != 0 by rewrite gt_eqF // sqrtr_gt0.
have hnz (q : TX) : OmT q -> Num.sqrt (T - q.1) != 0.
  by move=> hq; rewrite gt_eqF // sqrtr_gt0 subr_gt0.
have h := dgpr_first_field_compose (Dom := fun t : R^o => t != 0) (F := rt) (phi := fun t : R^o => t^-1)
  (c := - ((Num.sqrt (T - p.1))^-1 ^+ 2))
  hnz
  (dgpr_time_root_field hz0 hp)
  (scalar_reciprocal_differential hsq) (fun s => erefl).
rewrite scalerA in h; rewrite scalerA.
suff -> : irt p * (irt p * irt p) * - 2^-1 =
  - ((Num.sqrt (T - p.1))^-1 ^+ 2) * (2 * Num.sqrt (T - p.1))^-1 by exact h.
rewrite invfM /=; set u := (Num.sqrt (T - p.1))^-1; rewrite expr2; ring.
Qed.

(** Source for [dgpr_time_inverse_root_bound]: the derivatives of
    [(t,x) |-> (T - t)^(-1/2)] are bounded on the strip a <= t <= b,
    b < T: by induction on the order, from Dg = -(1/2) g^3 D(T - t);
    proof of lem:regularity. *)
Theorem dgpr_time_inverse_root_bound (j : nat) : WDY C1 irt j.
Proof.
have [z0 hz0] := dgpr_time_first.
have [_ hg] := dgpr_time_root_class.
have hgg : norm_class_all_orders hNT hA OmT (fun p => irt p * irt p : R^o).
  by move=> k; exact: (norm_class_scalar_product (hg k) (hg k)).
have hP : norm_class_all_orders hNT hA OmT (fun p => irt p * (irt p * irt p) : R^o).
  by move=> k; exact: (norm_class_scalar_product (hg k) (hgg k)).
have hF1c := norm_class_infinity_constant hNT hZ1 (fun j => hW j) hAo ((- 2^-1) *: z0).
have hstep k : (forall i, (i <= k)%N -> WDY C1 irt i) ->
    forall i, (i <= k)%N -> WDY C1 (fun p => irt p * (irt p * irt p) : R^o) i.
  move=> hk i hi.
  have hgi i' : (i' <= i)%N -> WDY C1 irt i' := fun hi' => hk i' (leq_trans hi' hi).
  have hg2 i' : (i' <= i)%N -> WDY C1 (fun p => irt p * irt p : R^o) i'.
    move=> hi'.
    exact: (@dgpr_bilinear_weighted_derivative R TX NT hNT OmT K0 C1 C1 C1 dgpr_one_product dgpr_one_sum i'
      R^o R^o R^o A1 A1 A1 hA hA hA _ _ _ _ _ _ _ _ _ (fun j => hZ j) (fun j => hZ j) (fun j => hZ j)
      irt irt (fun s t : R^o => s * t : R^o) (dgpr_scalar_mul_bilinear R) (hg i') (hg i')
      (fun i'' h'' => hgi i'' (leq_trans h'' hi')) (fun i'' h'' => hgi i'' (leq_trans h'' hi'))).
  exact: (@dgpr_bilinear_weighted_derivative R TX NT hNT OmT K0 C1 C1 C1 dgpr_one_product dgpr_one_sum i
    R^o R^o R^o A1 A1 A1 hA hA hA _ _ _ _ _ _ _ _ _ (fun j => hZ j) (fun j => hZ j) (fun j => hZ j)
    irt (fun p => irt p * irt p : R^o) (fun s t : R^o => s * t : R^o) (dgpr_scalar_mul_bilinear R)
    (hg i) (hgg i) hgi hg2).
have hTb : 0 < T - b by rewrite subr_gt0.
have hc : 0 < (Num.sqrt (T - b))^-1 + 1 by rewrite ltr_wpDl // invr_ge0 sqrtr_ge0.
have h0 : WDY C1 irt 0.
  apply: (dgpr_weighted_zero hNT hA (w := fun p => dgpr_polynomial_weight ((Num.sqrt (T - b))^-1 + 1) (N p.2) * 1)).
    exact: dgpr_relative_weight hc (fun _ _ => ler01).
  move=> p hp hpo; rewrite mulr1.
  apply: le_trans (dgpr_polynomial_weight_one (ltW hc) (inner_norm_nonnegative _ _)).
  have hs : 0 < T - p.1 by rewrite subr_gt0.
  rewrite ger0_norm ?invr_ge0 ?sqrtr_ge0 //.
  apply: le_trans (_ : (Num.sqrt (T - b))^-1 <= _); last by rewrite lerDl.
  rewrite lef_pV2 ?posrE ?sqrtr_gt0 // ler_sqrt; last exact: ltW.
  by case/andP: hp => _ hpb; rewrite lerD2l lerN2.
exact: (dgpr_weighted_relation dgpr_one_product dgpr_one_sum hP hF1c (dgpr_time_inverse_root_field hz0)
  (dgpr_time_constant_field _) hstep h0).
Qed.

(** Source for [dgpr_time_root_bound]: the derivatives of
    [(t,x) |-> (T - t)^(1/2)] are bounded on the strip a <= t <= b,
    b < T, since D (T - t)^(1/2) = (T - t)^(-1/2) times -(1/2) D(T - t);
    proof of lem:regularity. *)
Theorem dgpr_time_root_bound (j : nat) : WDY C1 rt j.
Proof.
have [z0 hz0] := dgpr_time_first.
have [_ hg] := dgpr_time_root_class.
have hF1c := norm_class_infinity_constant hNT hZ1 (fun j => hW j) hAo (2^-1 *: z0).
have hfield p : OmT p -> HD OmT rt 1 p (irt p *: (2^-1 *: z0)).
  move=> hp; have h := dgpr_time_root_field hz0 hp.
  by rewrite scalerA -invfM mulrC.
have hc : 0 < Num.sqrt (T - a) + 1 by rewrite ltr_wpDl // sqrtr_ge0.
have h0 : WDY C1 rt 0.
  apply: (dgpr_weighted_zero hNT hA (w := fun p => dgpr_polynomial_weight (Num.sqrt (T - a) + 1) (N p.2) * 1)).
    exact: dgpr_relative_weight hc (fun _ _ => ler01).
  move=> p hp hpo; rewrite mulr1.
  apply: le_trans (dgpr_polynomial_weight_one (ltW hc) (inner_norm_nonnegative _ _)).
  rewrite ger0_norm ?sqrtr_ge0 //.
  apply: le_trans (_ : Num.sqrt (T - a) <= _); last by rewrite lerDl.
  by apply: ler_wsqrtr; case/andP: hp => hap _; rewrite lerD2l lerN2.
exact: (dgpr_weighted_relation dgpr_one_product dgpr_one_sum hg hF1c hfield
  (dgpr_time_constant_field _) (fun k _ i _ => dgpr_time_inverse_root_bound i) h0).
Qed.
End TimeFactors.
