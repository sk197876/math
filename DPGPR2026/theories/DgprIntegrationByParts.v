(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    section 3, lem:ibp, DPGPR (3.17): the integration by parts identity
    - ∫ rho D^2 log rho(e,e) dL^n
      = ∫ rho [(div e + D log rho(e))^2 - trace(De ∘ De)] dL^n
    in the first case of the blueprint proof, where e is twice
    differentiable with polynomial bounds. The proof applies
    lem:classes(cl:div) to the maps b rho e and rho De(e), coordinate by
    coordinate. The general case (locally Lipschitzian e, by mollification)
    is not formalised; see docs/classes-ibp.md. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness FiniteCoordinates LinearBasis
  FiniteDualDimension EuclideanCoordinateMetric EuclideanTraceContinuity
  NormDifferentialUP NormClassOneUP NormClassZeroArithmetic NormClassZeroScalarProduct
  NormClassZeroFiniteSum MeasureUP MeasurableFunctionUP MeasureIntegralUP
  SummableRealFunctionUP SummableRealArithmetic EuclideanLebesgueDimensions
  RealExponentialUP RealExponentialSealed RealExponentialLaws RealPower.
From DPGPR Require Import DgprGrowthClasses DgprLebesgueIntegrals DgprDivergenceIntegral.
From DPGPR Require Import DgprDifferentialCalculus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Absorb.
Variable R : realType.

(** Source for [dgpr_polynomial_power_weight]: def:classes: a power of
    k + c(1 + r)^c is bounded by a polynomial weight. *)
Lemma dgpr_polynomial_power_weight (k c : R) (m : nat) : 0 < k -> 0 < c ->
  exists c', 0 < c' /\ forall r, 0 <= r ->
    (k + dgpr_polynomial_weight c r) ^+ m <= dgpr_polynomial_weight c' r.
Proof.
move=> hk hc.
have h1 r : 0 <= r -> k + dgpr_polynomial_weight c r <= dgpr_polynomial_weight (k + c) r.
  move=> hr; apply: le_trans (dgpr_polynomial_weight_sum hk hc hr).
  by rewrite lerD2r; apply: dgpr_polynomial_weight_one => //; exact: ltW.
elim: m=> [|m [cm [hcm hm]]].
- exists 1; split=> // r hr; rewrite expr0.
  exact: dgpr_polynomial_weight_one.
- have hkc : 0 < k + c by rewrite addr_gt0.
  exists (1 * cm * (k + c) + cm + (k + c)); split.
    by have := mulr_gt0 hcm hkc; rewrite mul1r; lra.
  move=> r hr; rewrite exprS mulrC.
  apply: le_trans (dgpr_polynomial_weight_product ler01 hcm hkc hr); rewrite mul1r.
  have hP := dgpr_polynomial_weight_nonnegative r (ltW hc).
  apply: ler_pM.
  + by apply: exprn_ge0; have := ltW hk; lra.
  + by have := ltW hk; lra.
  + exact: hm.
  + exact: h1.
Qed.

(** Source for [dgpr_gaussian_absorbs]: the inequality
    (1 + |x|)^c exp(-|x|^2/c') <= c'' exp(-|x|^2/c'') in the proof of
    lem:classes, blueprint section 3, for a multiple of a power of
    k + c(1 + r)^c. *)
Lemma dgpr_gaussian_absorbs (K k c : R) (m : nat) : 0 <= K -> 0 < k -> 0 < c ->
  exists c', 0 < c' /\ forall r, 0 <= r ->
    K * ((k + dgpr_polynomial_weight c r) ^+ m * dgpr_gaussian_weight c r) <=
      dgpr_gaussian_weight c' r.
Proof.
move=> hK hk hc; have [cm [hcm hm]] := dgpr_polynomial_power_weight m hk hc.
exists (dgpr_polynomial_gaussian_constant K cm c); split.
  exact: dgpr_polynomial_gaussian_constant_positive.
move=> r hr; apply: le_trans (dgpr_polynomial_gaussian_weight_product hK hcm hc hr).
apply: (ler_wpM2l hK); apply: (ler_wpM2r _ (hm r hr)).
exact: (dgpr_gaussian_weight_nonnegative r (ltW hc)).
Qed.
End Absorb.

Section IbpSmooth.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Local Notation NR := (fun t : R^o => `|t|).
Local Notation hNR := (@scalar_absolute_value_norm R).
Local Notation eps := (@coordinate_basis R n).

(** Source for [dgpr_directional_integral_values]: lem:classes(cl:div)
    for a single direction, with the differential given by its values. *)
Lemma dgpr_directional_integral_values (phi : X -> R) (l : X -> X -> R) (c : R) (v : X) :
  0 < c -> (forall x, dgpr_differential_values NR phi x (l x)) ->
  (forall x, exists L, 0 <= L /\ `|phi x| + L <= dgpr_gaussian_weight c (NX x) /\
     forall w, `|l x w| <= L * NX w) ->
  is_measure_integral mu (real_total_integrand (fun x => l x v)) 0%:E.
Proof.
move=> hc hd hb; have [D hD] := choice hd.
have hdiff x : has_norm_differential NX NR setT phi x (D x) by have [] := hD x.
have hbD x : exists L, 0 <= L /\ `|phi x| + L <= dgpr_gaussian_weight c (NX x) /\
    forall w, `|D x w| <= L * NX w.
  have [L [hL0 [hL hLw]]] := hb x; exists L; split=> //; split=> // w.
  by have [_ ->] := hD x; exact: hLw.
have h := dgpr_directional_integral v hc hdiff hbD.
have -> : (fun x => l x v) = (fun x => D x v) by apply: funext=> x; have [_ ->] := hD x.
exact: h.
Qed.

(** Source for [dgpr_ibp_smooth]: lem:ibp, first case of the proof
    (DPGPR (3.17)), with h = log rho given through its first and second
    differentials H1 = Dh and H2 = D(Dh), and e given through De and
    E2 = D(De), which is symmetric. *)
Theorem dgpr_ibp_smooth (rho : X -> R) (H1 : X -> Hom X R^o) (H2 : X -> Hom X (Hom X R^o))
    (e : X -> X) (De : X -> Hom X X) (E2 : X -> Hom X (Hom X X)) (c : R) :
  0 < c -> (forall x, 0 < rho x) ->
  (forall x, rho x <= dgpr_gaussian_weight c (NX x)) ->
  (forall x, dgpr_differential_values NR rho x (fun v => rho x * H1 x v)) ->
  (forall x w, dgpr_differential_values NR (fun y => H1 y w) x (fun v => H2 x v w)) ->
  (forall x, dgpr_differential_values NX e x (fun v => De x v)) ->
  (forall x w, dgpr_differential_values NX (fun y => De y w) x (fun v => E2 x v w)) ->
  (forall x v w, E2 x v w = E2 x w v) ->
  (forall v w, norm_class_zero NX NR setT (fun x => H2 x v w)) ->
  (forall x v w, NX (e x) <= dgpr_polynomial_weight c (NX x) /\
     NX (De x v) <= dgpr_polynomial_weight c (NX x) * NX v /\
     NX (E2 x v w) <= dgpr_polynomial_weight c (NX x) * (NX v * NX w) /\
     `|H1 x v| <= dgpr_polynomial_weight c (NX x) * NX v /\
     `|H2 x v w| <= dgpr_polynomial_weight c (NX x) * (NX v * NX w)) ->
  exists a : R,
    is_measure_integral mu (real_total_integrand
      (fun x => - (rho x * H2 x (e x) (e x)))) a%:E /\
    is_measure_integral mu (real_total_integrand
      (fun x => rho x * ((dgpr_divergence (De x) + H1 x (e x)) ^+ 2 -
        dgpr_divergence (hom_comp (De x) (De x))))) a%:E.
Proof.
move=> hc hpos hgauss hrho hH1 he hDe hsym hH2c hbd.
pose E (j : 'I_n) (x : X) : R := e x j.
pose dE (j : 'I_n) (x v : X) : R := De x v j.
pose dive (x : X) : R := \sum_i De x (eps i) i.
pose ddive (x v : X) : R := \sum_i E2 x v (eps i) i.
pose He (x : X) : R := H1 x (e x).
pose dHe (x v : X) : R := H2 x v (e x) + H1 x (De x v).
pose b (x : X) : R := dive x + He x.
pose db (x v : X) : R := ddive x v + dHe x v.
pose phi (j : 'I_n) (x : X) : R := b x * (rho x * E j x).
pose dphi (j : 'I_n) (x v : X) : R :=
  db x v * (rho x * E j x) + b x * (rho x * H1 x v * E j x + rho x * dE j x v).
pose psi (j : 'I_n) (x : X) : R := rho x * De x (e x) j.
pose dpsi (j : 'I_n) (x v : X) : R :=
  rho x * H1 x v * De x (e x) j + rho x * (E2 x v (e x) j + De x (De x v) j).
(* differentials *)
have hE j x : dgpr_differential_values NR (E j) x (dE j x).
  have h := dgpr_values_coordinate j (he x); exact h.
have hdive x : dgpr_differential_values NR dive x (ddive x).
  have h := dgpr_values_sum hNR (fun i => dgpr_values_coordinate i (hDe x (eps i))).
  exact h.
have hHe x : dgpr_differential_values NR He x (dHe x).
  have h := dgpr_values_evaluation hNR (hH1 x) (he x); exact h.
have hb x : dgpr_differential_values NR b x (db x).
  have h := dgpr_values_add hNR (hdive x) (hHe x); exact h.
have hphi j x : dgpr_differential_values NR (phi j) x (dphi j x).
  have h1 := dgpr_values_scalar_product hNR (hrho x) (hE j x).
  have h2 := dgpr_values_scalar_product hNR (hb x) h1.
  apply: (dgpr_values_ext _ _ h2)=> [y|v] //.
have hDee x : dgpr_differential_values NX (fun y => De y (e y)) x
    (fun v => E2 x v (e x) + De x (De x v)).
  have h := dgpr_values_evaluation hNX (hDe x) (he x); exact h.
have hpsi j x : dgpr_differential_values NR (psi j) x (dpsi j x).
  have h1 := dgpr_values_coordinate j (hDee x).
  have h2 := dgpr_values_scalar_product hNR (hrho x) h1.
  apply: (dgpr_values_ext _ _ h2)=> [y|v] //.
  by rewrite /dpsi ffunE.
have hscal (a d : R) : a *: (d : R^o) = a * d by [].
have hS1 x : \sum_j dphi j x (eps j) = rho x * db x (e x) + rho x * b x * (He x + dive x).
  rewrite /dphi big_split /=; congr (_ + _).
  - rewrite -(dgpr_values_linear (e x) (hb x)) mulr_sumr; apply: eq_bigr=> j _.
    by rewrite hscal /E; ring.
  - rewrite /He /dive -(dgpr_coordinate_sum (H1 x) (e x)) mulrDr !mulr_sumr -big_split /=.
    by apply: eq_bigr=> j _; rewrite hscal /E /dE; ring.
have hS2 x : \sum_j dpsi j x (eps j) =
    rho x * H1 x (De x (e x)) + rho x * ddive x (e x) +
      rho x * dgpr_divergence (hom_comp (De x) (De x)).
  rewrite /dpsi big_split /= -(dgpr_coordinate_sum (H1 x) (De x (e x))) mulr_sumr.
  rewrite dgpr_divergenceE /ddive -addrA; congr (_ + _).
    by apply: eq_bigr=> j _; rewrite hscal; ring.
  rewrite !mulr_sumr -big_split /=; apply: eq_bigr=> j _.
  by rewrite (hsym x (eps j) (e x)); ring.
have hdiff x : \sum_j dphi j x (eps j) - \sum_j dpsi j x (eps j) =
    rho x * H2 x (e x) (e x) + rho x * ((dgpr_divergence (De x) + H1 x (e x)) ^+ 2 -
      dgpr_divergence (hom_comp (De x) (De x))).
  by rewrite hS1 hS2 !dgpr_divergenceE /db /dHe /b /He /dive; ring.
(* pointwise bounds *)
have hN := inner_norm_nonnegative (@euclidean_inner_productP R n).
pose P (x : X) : R := dgpr_polynomial_weight c (NX x).
pose W (x : X) : R := n%:R + 1 + P x.
have hn0 : (0 : R) <= n%:R := ler0n _ _.
have hP0 x : 0 <= P x := dgpr_polynomial_weight_nonnegative (NX x) (ltW hc).
have hW1 x : 1 <= W x by rewrite /W; have := hP0 x; lra.
have hW0 x : 0 <= W x by have := hW1 x; lra.
have hPW x : P x <= W x by rewrite /W; lra.
have hnW x : n%:R * P x <= W x ^+ 2.
  by rewrite expr2; apply: ler_pM=> //; rewrite /W; have := hP0 x; lra.
have hPP x : P x * P x <= W x ^+ 2 by rewrite expr2; apply: ler_pM.
have hepsN i : NX (eps i) = 1 := @euclidean_coordinate_unit_norm R n i.
have hcoord (y : X) i : `|y i| <= NX y := euclidean_coordinate_norm_bound i y.
have hrho0 x : 0 <= rho x := ltW (hpos x).
have he1 x : NX (e x) <= P x by have [] := hbd x 0 0.
have hDe1 x v : NX (De x v) <= P x * NX v by have [_ []] := hbd x v 0.
have hE21 x v w : NX (E2 x v w) <= P x * (NX v * NX w) by have [_ [_ []]] := hbd x v w.
have hH11 x v : `|H1 x v| <= P x * NX v by have [_ [_ [_ []]]] := hbd x v 0.
have hH21 x v w : `|H2 x v w| <= P x * (NX v * NX w) by have [_ [_ [_ [_ ]]]] := hbd x v w.
have hsumP x (F : 'I_n -> R) a : (forall i, `|F i| <= P x * a) -> 0 <= a ->
    `|\sum_i F i| <= W x ^+ 2 * a.
  move=> hF ha; apply: le_trans (ler_norm_sum _ _ _) _.
  apply: le_trans (ler_sum _ (fun i _ => hF i)) _.
  by rewrite sumr_const card_ord -mulr_natl mulrA; apply: ler_wpM2r=> //.
have bE j x : `|E j x| <= W x.
  by apply: le_trans (hcoord _ _) _; apply: le_trans (he1 x) (hPW x).
have bdE j x w : `|dE j x w| <= W x * NX w.
  apply: le_trans (hcoord _ _) _; apply: le_trans (hDe1 x w) _.
  exact: (ler_wpM2r (hN w) (hPW x)).
have bH1 x w : `|H1 x w| <= W x * NX w.
  by apply: le_trans (hH11 x w) _; exact: (ler_wpM2r (hN w) (hPW x)).
have bdive x : `|dive x| <= W x ^+ 2.
  rewrite -[X in _ <= X]mulr1; apply: hsumP=> // i.
  apply: le_trans (hcoord _ _) _; apply: le_trans (hDe1 x _) _.
  by rewrite hepsN.
have bHe x : `|He x| <= W x ^+ 2.
  apply: le_trans (hH11 x (e x)) _; apply: le_trans (hPP x).
  exact: (ler_wpM2l (hP0 x) (he1 x)).
have bb x : `|b x| <= 2 * W x ^+ 2.
  by apply: le_trans (ler_normD _ _) _; have := bdive x; have := bHe x; lra.
have bddive x w : `|ddive x w| <= W x ^+ 2 * NX w.
  apply: hsumP=> // i.
  apply: le_trans (hcoord _ _) _; apply: le_trans (hE21 x w _) _.
  by rewrite hepsN mulr1.
have hPPa x a : 0 <= a -> P x * (a * NX (e x)) <= W x ^+ 2 * a.
  move=> ha; apply: le_trans (_ : P x * (a * P x) <= _).
    by apply: (ler_wpM2l (hP0 x)); exact: (ler_wpM2l ha (he1 x)).
  have -> : P x * (a * P x) = (P x * P x) * a by ring.
  exact: (ler_wpM2r ha (hPP x)).
have hPPb x (w : X) : P x * NX (De x w) <= W x ^+ 2 * NX w.
  apply: le_trans (ler_wpM2l (hP0 x) (hDe1 x w)) _.
  by rewrite mulrA; exact: (ler_wpM2r (hN w) (hPP x)).
have bdHe x w : `|dHe x w| <= 2 * W x ^+ 2 * NX w.
  apply: le_trans (ler_normD _ _) _.
  have h1 : `|H2 x w (e x)| <= W x ^+ 2 * NX w.
    exact: le_trans (hH21 x w (e x)) (hPPa x (NX w) (hN w)).
  have h2 : `|H1 x (De x w)| <= W x ^+ 2 * NX w.
    exact: le_trans (hH11 x (De x w)) (hPPb x w).
  by rewrite /dHe; lra.
have bdb x w : `|db x w| <= 3 * W x ^+ 2 * NX w.
  apply: le_trans (ler_normD _ _) _.
  by have := bddive x w; have := bdHe x w; lra.
have bDee j x : `|De x (e x) j| <= W x ^+ 2.
  apply: le_trans (hcoord _ _) _; apply: le_trans (hDe1 x (e x)) _.
  by apply: le_trans (hPP x); exact: (ler_wpM2l (hP0 x) (he1 x)).
have bE2e j x w : `|E2 x w (e x) j| <= W x ^+ 2 * NX w.
  apply: le_trans (hcoord _ _) _.
  exact: le_trans (hE21 x w (e x)) (hPPa x (NX w) (hN w)).
have bDDe j x w : `|De x (De x w) j| <= W x ^+ 2 * NX w.
  apply: le_trans (hcoord _ _) _.
  exact: le_trans (hDe1 x (De x w)) (hPPb x w).
have hW34 x : W x ^+ 3 <= W x ^+ 4 by apply: ler_weXn2l; [exact: hW1|].
have hW24 x : W x ^+ 2 <= W x ^+ 4 by apply: ler_weXn2l; [exact: hW1|].
have hrhoW x (k : nat) : 0 <= W x ^+ k * rho x.
  by apply: mulr_ge0; [apply: exprn_ge0; exact: hW0|exact: hrho0].
have bphi j x : exists L, 0 <= L /\ `|phi j x| + L <= 9 * (W x ^+ 4 * rho x) /\
    forall w, `|dphi j x w| <= L * NX w.
  exists (7 * (W x ^+ 4 * rho x)); split.
    by apply: mulr_ge0=> //; exact: hrhoW.
  have hER : `|rho x * E j x| <= rho x * W x.
    by rewrite normrM ger0_norm //; exact: (ler_wpM2l (hrho0 x) (bE j x)).
  split.
  - have h1 : `|phi j x| <= 2 * W x ^+ 2 * (rho x * W x).
      by rewrite /phi normrM; apply: ler_pM; [exact: normr_ge0|exact: normr_ge0|exact: bb|exact: hER].
    have h3 : 0 <= (W x ^+ 4 - W x ^+ 3) * rho x.
      by apply: mulr_ge0; [have := hW34 x; lra|exact: hrho0].
    have hW3 : W x ^+ 3 = W x ^+ 2 * W x by rewrite exprSr.
    have hW4 : W x ^+ 4 = W x ^+ 3 * W x by rewrite exprSr.
    rewrite hW4 hW3 in h3 *; nra.
  - move=> w.
    have hw := hN w.
    have h1 : `|dphi j x w| <= 3 * W x ^+ 2 * NX w * (rho x * W x) +
        2 * W x ^+ 2 * (rho x * (W x * NX w) * W x + rho x * (W x * NX w)).
      rewrite /dphi; apply: le_trans (ler_normD _ _) _; apply: lerD.
      + by rewrite normrM; apply: ler_pM; [exact: normr_ge0|exact: normr_ge0|exact: bdb|exact: hER].
      + rewrite normrM; apply: ler_pM; [exact: normr_ge0|exact: normr_ge0|exact: bb|].
        apply: le_trans (ler_normD _ _) _; apply: lerD.
        * rewrite normrM; apply: ler_pM; [exact: normr_ge0|exact: normr_ge0| |exact: bE].
          by rewrite normrM ger0_norm //; exact: (ler_wpM2l (hrho0 x) (bH1 x w)).
        * by rewrite normrM ger0_norm //; exact: (ler_wpM2l (hrho0 x) (bdE j x w)).
    apply: le_trans h1 _.
    have h3 : 0 <= (W x ^+ 4 - W x ^+ 3) * (rho x * NX w).
      by apply: mulr_ge0; [have := hW34 x; lra|apply: mulr_ge0=> //; exact: hrho0].
    have hW3 : W x ^+ 3 = W x ^+ 2 * W x by rewrite exprSr.
    have hW4 : W x ^+ 4 = W x ^+ 3 * W x by rewrite exprSr.
    rewrite hW4 hW3 in h3 *; nra.
have bpsi j x : exists L, 0 <= L /\ `|psi j x| + L <= 9 * (W x ^+ 4 * rho x) /\
    forall w, `|dpsi j x w| <= L * NX w.
  exists (3 * (W x ^+ 4 * rho x)); split.
    by apply: mulr_ge0=> //; exact: hrhoW.
  have h2 : 0 <= (W x ^+ 4 - W x ^+ 2) * rho x.
    by apply: mulr_ge0; [have := hW24 x; lra|exact: hrho0].
  split.
  - have h1 : `|psi j x| <= rho x * W x ^+ 2.
      by rewrite /psi normrM ger0_norm //; exact: (ler_wpM2l (hrho0 x) (bDee j x)).
    have := hrhoW x 4; nra.
  - move=> w; have hw := hN w.
    have h1 : `|dpsi j x w| <= rho x * (W x * NX w) * W x ^+ 2 +
        rho x * (W x ^+ 2 * NX w + W x ^+ 2 * NX w).
      rewrite /dpsi; apply: le_trans (ler_normD _ _) _; apply: lerD.
      + rewrite normrM; apply: ler_pM; [exact: normr_ge0|exact: normr_ge0| |exact: bDee].
        by rewrite normrM ger0_norm //; exact: (ler_wpM2l (hrho0 x) (bH1 x w)).
      + rewrite normrM ger0_norm //; apply: (ler_wpM2l (hrho0 x)).
        apply: le_trans (ler_normD _ _) _; apply: lerD; [exact: bE2e|exact: bDDe].
    apply: le_trans h1 _.
    have h3 : 0 <= (W x ^+ 4 - W x ^+ 3) * (rho x * NX w).
      by apply: mulr_ge0; [have := hW34 x; lra|apply: mulr_ge0=> //; exact: hrho0].
    have h4 : 0 <= (W x ^+ 4 - W x ^+ 2) * (rho x * NX w).
      by apply: mulr_ge0; [have := hW24 x; lra|apply: mulr_ge0=> //; exact: hrho0].
    have hW3 : W x ^+ 3 = W x ^+ 2 * W x by rewrite exprSr.
    rewrite hW3 in h3; nra.
(* the Gaussian bound *)
have h9 : (0 : R) <= 9 by [].
have hk : (0 : R) < n%:R + 1 by have := hn0; lra.
have [cg [hcg hcgb]] := @dgpr_gaussian_absorbs R 9 (n%:R + 1) c 4 h9 hk hc.
have hG x : 9 * (W x ^+ 4 * rho x) <= dgpr_gaussian_weight cg (NX x).
  apply: le_trans (hcgb (NX x) (hN x)); apply: (ler_wpM2l h9).
  apply: (ler_wpM2l (exprn_ge0 4 (hW0 x))); exact: hgauss.
have hI1 : is_measure_integral mu (real_total_integrand
    (fun x => \sum_j dphi j x (eps j))) 0%:E.
  apply: dgpr_integral_zero_sum=> j.
  apply: (dgpr_directional_integral_values (eps j) hcg (hphi j))=> x.
  have [L [hL0 [hL hLw]]] := bphi j x.
  by exists L; split=> //; split=> //; apply: le_trans hL (hG x).
have hI2 : is_measure_integral mu (real_total_integrand
    (fun x => \sum_j dpsi j x (eps j))) 0%:E.
  apply: dgpr_integral_zero_sum=> j.
  apply: (dgpr_directional_integral_values (eps j) hcg (hpsi j))=> x.
  have [L [hL0 [hL hLw]]] := bpsi j x.
  by exists L; split=> //; split=> //; apply: le_trans hL (hG x).
(* the integrand rho D^2 h(e,e) is continuous and dominated *)
have hcont (f : X -> R) (l : X -> X -> R) :
    (forall x, dgpr_differential_values NR f x (l x)) -> norm_class_zero NX NR setT f.
  move=> h; have [D hD] := choice h.
  apply: dgpr_continuous_class_zero; apply: (@dgpr_differentiable_continuous R n f D).
  by move=> x; have [] := hD x.
have hint : forall x, setT x -> norm_domain_interior NX setT x.
  by move=> x _; exists 1; split.
have hsumE (L : 'I_n -> Hom X R^o) w : (\sum_i L i) w = \sum_i L i w.
  by elim/big_rec2: _=> [|i y g _ <-]; rewrite ?hom_addE ?hom_zeroE.
pose F2 (x : X) : R := \sum_i e x i * \sum_j e x j * H2 x (eps i) (eps j).
have hF2 x : H2 x (e x) (e x) = F2 x.
  have h := congr1 (fun L : Hom X R^o => L (e x)) (dgpr_coordinate_sum (H2 x) (e x)).
  rewrite /= hsumE in h; rewrite -h /F2; apply: eq_bigr=> i _.
  by rewrite hom_scaleE -(dgpr_coordinate_sum (H2 x (eps i)) (e x)).
have hF2c : norm_class_zero NX NR setT F2.
  apply: (@norm_class_zero_finite_sum R X R^o NX NR hNX hNR setT 'I_n
    (fun i x => e x i * \sum_j e x j * H2 x (eps i) (eps j)) hint)=> i.
  apply: (@norm_class_zero_scalar_product R X R^o NX NR hNR setT (E i)
    (fun x => \sum_j e x j * H2 x (eps i) (eps j))); first exact: hcont _ _ (hE i).
  apply: (@norm_class_zero_finite_sum R X R^o NX NR hNX hNR setT 'I_n
    (fun j x => e x j * H2 x (eps i) (eps j)) hint)=> j.
  apply: (@norm_class_zero_scalar_product R X R^o NX NR hNR setT (E j)
    (fun x => H2 x (eps i) (eps j))); first exact: hcont _ _ (hE j).
  exact: hH2c.
have hRc : norm_class_zero NX NR setT (fun x => rho x * H2 x (e x) (e x)).
  have h := @norm_class_zero_scalar_product R X R^o NX NR hNR setT rho F2
    (hcont _ _ hrho) hF2c.
  have -> : (fun x => rho x * H2 x (e x) (e x)) = (fun x => rho x *: (F2 x : R^o)).
    by apply: funext=> x; rewrite hF2.
  exact: h.
have hRb x : `|rho x * H2 x (e x) (e x)| <= dgpr_gaussian_weight cg (NX x).
  apply: le_trans (hG x); rewrite normrM ger0_norm; last exact: hrho0.
  have h1 : `|H2 x (e x) (e x)| <= W x ^+ 4.
    apply: le_trans (hH21 x _ _) _.
    apply: le_trans (_ : P x * (P x * P x) <= _).
      by apply: (ler_wpM2l (hP0 x)); apply: ler_pM; [exact: hN|exact: hN|exact: he1|exact: he1].
    apply: le_trans _ (hW34 x); rewrite exprSr mulrC.
    by apply: ler_pM; [apply: mulr_ge0; exact: hP0|exact: hP0|exact: hPP|exact: hPW].
  have := hrhoW x 4; have := hrho0 x; nra.
have [a0 ha0] := dgpr_dominated_summable (dgpr_continuous_measurable hRc)
  (dgpr_gaussian_weight_summable n hcg) hRb.
exists (- a0); split.
- have h := real_total_integral_scale hm (-1) ha0.
  rewrite mulN1r in h; apply: (eq_rect _ (fun F => is_measure_integral mu (real_total_integrand F) _) h).
  by apply: funext=> x; rewrite mulN1r.
- have h3 := real_total_integral_subtract hm hI1 hI2.
  have h4 := real_total_integral_subtract hm h3 ha0.
  rewrite !subrr sub0r in h4.
  apply: (eq_rect _ (fun F => is_measure_integral mu (real_total_integrand F) _) h4).
  by apply: funext=> x; rewrite hdiff; ring.
Qed.

End IbpSmooth.
