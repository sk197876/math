(** Federer (1969), 4.1.23, p. 380:
    the transverse atomic zero-chain has exactly
    the total positive weight. A single original
    compact unit test equal to one on
    B gives the lower mass bound; positivity
    gives the matching upper bound, even when
    some tags coincide or weights vanish. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms AlternatingZero CurrentCoefficientNorms
  CurrentZeroCovectorMaps CurrentSpaces CurrentPointEvaluation CurrentDirac
  DiracCurrentBounds CurrentSupportGeometry CurrentBoundedNeighbourhoodTest
  CurrentMassUP CurrentMassSealed CurrentMassBasic CurrentGlobalComassBound
  CurrentGlobalComassSealed ExtendedSupremumUP CurrentFiniteMassRepresentation
  NormalCurrentsUP SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PositiveAtomicMass.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation C := (@current_space R h2 n Full hFull 0%N).
Local Notation DT := (@current_test_space R h2 n Full hFull 0%N).
Local Notation action := (@current_value R h2 n Full hFull 0%N).
Local Notation ev := (@current_test_value R h2 n Full hFull 0%N).
Local Notation M := (@CurrentMass.value R h2 n 0%N Full hFull).
Local Notation support := (@current_support R h2 n Full hFull 0%N).
Local Notation point := (@dirac_current R h2 n Full hFull).

(** Source for [positive_atomic_zero_current]: the
    literal finite chain Q=sum_k Leb(B_k)[b_k]
    in Federer 4.1.23, p. 380.
    The coefficients and original point currents
    remain visible; no alternate measure representation
    is used to define Q. *)
Definition positive_atomic_zero_current (I : finType) (tag : I -> X) (a : I -> R) : C :=
  \sum_i a i*:point (tag i).

(** Source for [positive_atomic_zero_current_mass]: the
    exact equality M(Q)=sum_k Leb(B_k)
    of Federer 4.1.23, p. 380.
    All positive finite weights are retained,
    including zero weights and an empty family.
    The actual zero-chain is normal and
    supported in the same original B. *)
Theorem positive_atomic_zero_current_mass (B : smooth_compact_set hNX Full)
    (I : finType) (tag : I -> X) (a : I -> R) :
  (forall i, smooth_compact_carrier B (tag i)) -> (forall i, 0<=a i) ->
  M (positive_atomic_zero_current tag a)=(\sum_i a i)%:E /\
    @normal_currents_supported_in R h2 n Full hFull 0%N B
      (positive_atomic_zero_current tag a).
Proof.
move=> hTags hWeights.
pose Q := positive_atomic_zero_current tag a.
have hAction (psi : DT) : action Q psi=\sum_i a i*zero_form_value (ev psi (tag i)).
  rewrite /Q /positive_atomic_zero_current current_value_finite_sum.
  apply: eq_bigr=> i _; by rewrite current_value_scale dirac_current_evaluation.
have hUpper : (M Q<=(\sum_i a i)%:E)%E.
  apply: (extended_supremum_least (@CurrentMass.laws R h2 n 0%N Full hFull Q))
    => z [psi [hUnit <-]].
  rewrite lee_fin hAction; apply: ler_sum=> i _.
  have hComass := (@current_global_comass_bound R h2 n 0%N Full (ev psi) 1).1
    hUnit (tag i) Logic.I.
  rewrite current_zero_form_coefficient_norm in hComass.
  change (is_true (`|zero_form_value (ev psi (tag i))|<=1)) in hComass.
  have hCoefficient := le_trans (ler_norm (zero_form_value (ev psi (tag i)))) hComass.
  have h := ler_wpM2l (hWeights i) hCoefficient.
  by rewrite mulr1 in h.
have [gamma [_ [hRange hOne]]] := @current_bounded_neighbourhood_test_exists R h2 n
  B Full (@openT (real_norm_metric_space hNX)) (fun _ _ => Logic.I).
have hGamma : (@CurrentGlobalComass.value R h2 n 0%N Full (ev gamma)<=1)%E.
  apply: (@current_global_comass_bound R h2 n 0%N Full (ev gamma) 1).2=> x _.
  rewrite current_zero_form_coefficient_norm (ger0_norm (andP (hRange x)).1).
  exact: (andP (hRange x)).2.
have hCalibration : action Q gamma=\sum_i a i.
  rewrite hAction; apply: eq_bigr=> i _.
  by rewrite (@hOne (tag i) (hTags i)) zero_formK mulr1.
have hLower : ((\sum_i a i)%:E<=M Q)%E.
  rewrite -hCalibration.
  exact: (@current_mass_unit_test_upper R h2 n 0%N Full hFull Q gamma hGamma).
have hMass : M Q=(\sum_i a i)%:E.
  apply/eqP; rewrite eq_le; apply/andP; split; [exact: hUpper|exact: hLower].
have hSupport : support Q `<=` smooth_compact_carrier B.
  rewrite /Q /positive_atomic_zero_current; elim/big_rec: _=> [|i S _ hS].
  - exact: current_support_zero_subset.
  - apply: (@current_support_linear_subset R h2 n 0%N Full hFull B (a i)
      (point (tag i)) S _ hS)=> x hx.
    have hPoint := @dirac_current_support_subset R h2 n Full hFull (tag i) Logic.I x hx.
    by rewrite hPoint; exact: hTags i.
have hFinite : (M Q< +oo)%E by rewrite hMass ltry.
split; first exact: hMass.
split; last exact: hSupport.
split.
- split; last by [].
  exact: (@current_finite_mass_representation R h2 n 0%N Full hFull Q hFinite).
- exact: (@current_support_compact_bound R h2 n 0%N Full hFull B Q hSupport).
Qed.
End PositiveAtomicMass.
