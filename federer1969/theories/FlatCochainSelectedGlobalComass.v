(** Federer (1969), 4.1.19, p. 377: select
    bounded measurable representatives whose literal global
    comasses attain the cochain norm. The proof
    uses the already sharp pointwise choice and
    the exact essential pair norm, keeping those
    different quantities separate for arbitrary representatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentCoefficientNorms CurrentSpaces SmoothCompactSet
  CurrentFlatNorm FlatCurrentsUP FlatCurrentUnionSpace FlatCochainSpace
  CurrentLonePairImageUP CurrentLonePairFlatUP CurrentLonePairCost
  CompactContinuousVectorZeroExtension CurrentGlobalComassSealed
  CurrentGlobalComassBound BoundedCurrentFormGlobalComass
  FlatCochainRepresentationUP FlatCochainBoundedFormExistence
  FlatCochainFormEssentialNorm FlatCochainRepresentativeNorm
  BoundedCurrentFormEssentialRepresentative FlatCochainFormWeakEquation
  CurrentWeakExteriorPairUP EuclideanOpenDomainMeasure PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SelectedLiteralGlobalNorm.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y d := (A_m X R^o d).
Local Notation N d := (@current_form_comass R h2 n d).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation J := (@current_lone_pair_cost R h2 n m U hU).
Local Notation W := (@flat_current_union_space R h2 n m U hU).
Local Notation inc := (@flat_current_union_inclusion R h2 n m U hU).
Local Notation FK := (@current_flat_norm R h2 n m U hU).
Local Notation flatK := (@is_flat_current_supported_in R h2 n m U hU).
Local Notation A := (@flat_cochain_space R h2 n m U hU).
Local Notation F := (@flat_cochain_norm R h2 n m U hU).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Variable Q : Hom P W.
Hypothesis hQ : @is_current_lone_pair_flat_map R h2 n m U hU Q.
Hypothesis hFirst : forall v : P,
  exists K : smooth_compact_set hNX U,
    flatK K (inc (Q v)) /\ fine (FK K (inc (Q v)))<=J v.
Hypothesis hSecond : forall (K : smooth_compact_set hNX U) (T : W),
  flatK K (inc T) -> forall delta : R, 0<delta ->
  exists v : P, Q v=T /\ J v<=fine (FK K (inc T))+delta.

(** Source for [flat_cochain_selected_global_comass_exists]:
    the existential norm formula in Federer
    4.1.19, p. 377, has representatives
    with exactly the literal global-comass maximum.
    This supporting statement records nonempty U
    explicitly; the empty-domain global supremum is
    treated separately, without changing its old definition.
    No formula for arbitrary null modifications is assumed. *)
Theorem flat_cochain_selected_global_comass_exists (alpha : A) :
  (exists x, U x) ->
  exists phi : X -> Y m, exists psi : X -> Y m.+1,
    @is_flat_cochain_pair_density R h2 n m U hU Q alpha
      (fun x : UT => phi (set_val x))
      (fun x : UT => psi (set_val x)) /\
    @is_weak_current_exterior_pair R h2 n m U hU
      (fun x : UT => phi (set_val x))
      (fun x : UT => psi (set_val x)) /\
    (F alpha)%:E=Order.max (@CurrentGlobalComass.value R h2 n m U phi)
      (@CurrentGlobalComass.value R h2 n m.+1 U psi).
Proof.
move=> hNonempty.
have [p [q [hDensity [hPCap hQCap]]]] :=
  @flat_cochain_bounded_form_density_exists R h2 n m U hU Q hFirst alpha.
pose phi := @compact_vector_open_extension R XT U (Y m) p.
pose psi := @compact_vector_open_extension R XT U (Y m.+1) q.
have hPhiValues : (fun x : UT => phi (set_val x))=p.
  apply: funext=> x; exact: compact_vector_open_extension_value.
have hPsiValues : (fun x : UT => psi (set_val x))=q.
  apply: funext=> x; exact: compact_vector_open_extension_value.
have hPhiCap (x : X) (hx : U x) : N m (phi x)<=F alpha.
  pose a : UT := exist _ x (mem_set hx).
  change (is_true (N m (phi (set_val a))<=F alpha)).
  rewrite /phi compact_vector_open_extension_value; exact: hPCap.
have hPsiCap (x : X) (hx : U x) : N m.+1 (psi x)<=F alpha.
  pose a : UT := exist _ x (mem_set hx).
  change (is_true (N m.+1 (psi (set_val a))<=F alpha)).
  rewrite /psi compact_vector_open_extension_value; exact: hQCap.
have [a [hA [hPhiGlobal hAUpper]]] :=
  @current_bounded_form_global_comass_value R h2 n m U phi (F alpha)
    hNonempty hPhiCap.
have [b [hB [hPsiGlobal hBUpper]]] :=
  @current_bounded_form_global_comass_value R h2 n m.+1 U psi (F alpha)
    hNonempty hPsiCap.
have hPBound (x : UT) : N m (p x)<=a.
  have hGlobalBound : (@CurrentGlobalComass.value R h2 n m U phi<=a%:E)%E.
    by rewrite hPhiGlobal.
  have hCap := (@current_global_comass_bound R h2 n m U phi a).1 hGlobalBound.
  have h := @hCap (set_val x) (set_valP x).
  by rewrite /phi compact_vector_open_extension_value in h.
have hQBound (x : UT) : N m.+1 (q x)<=b.
  have hGlobalBound : (@CurrentGlobalComass.value R h2 n m.+1 U psi<=b%:E)%E.
    by rewrite hPsiGlobal.
  have hCap := (@current_global_comass_bound R h2 n m.+1 U psi b).1 hGlobalBound.
  have h := @hCap (set_val x) (set_valP x).
  by rewrite /psi compact_vector_open_extension_value in h.
have hPEss := @bounded_current_form_essential_bound R h2 n m U hU p a hA hPBound.
have hQEss := @bounded_current_form_essential_bound R h2 n m.+1 U hU q b hB hQBound.
have hExact := @flat_cochain_form_density_essential_norm R h2 n m U hU Q
  hFirst hSecond alpha p q hDensity.
have hLower : ((F alpha)%:E<=Order.max a%:E b%:E)%E.
  rewrite hExact /flat_cochain_representative_norm.
  exact: (le_max2 hPEss hQEss).
have hUpper : (Order.max a%:E b%:E<=(F alpha)%:E)%E.
  by rewrite ge_max !lee_fin hAUpper hBUpper.
have hGlobal : (F alpha)%:E=Order.max
    (@CurrentGlobalComass.value R h2 n m U phi)
    (@CurrentGlobalComass.value R h2 n m.+1 U psi).
  rewrite hPhiGlobal hPsiGlobal.
  apply/eqP; by rewrite eq_le hLower hUpper.
exists phi,psi; split.
- by rewrite hPhiValues hPsiValues.
split; last exact: hGlobal.
rewrite hPhiValues hPsiValues.
exact: (@flat_cochain_form_density_weak_equation R h2 n m U hU Q hQ alpha p q hDensity).
Qed.
End SelectedLiteralGlobalNorm.
