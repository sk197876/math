(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the exact original finite coefficient kernel is the original
    centre-vanishing ideal power. Reuse the finite monomial expansion
    of 3.1.11, p. 223, actual coefficient forms and the proved
    Hadamard/Leibniz connection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermRing AnalyticGermJetsSealed AnalyticGermCoefficientForms AnalyticVanishingIdealSealed
  SymmetricForms SymmetricMultiIndices SymmetricIndexBounds SymmetricDividedMonomials
  SymmetricMonomialTuples SymmetricFormCoordinateExpansion FiniteJetDegreeIndices
  AnalyticFiniteCoefficientsUP AnalyticVanishingJetProduct AnalyticVanishingPowerJets
  CommutativeIdealPowersSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Kernel.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable l:nat.
Variable a:X.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Local Notation W:=[the lmodType R of {ffun finite_jet_degree_indices n l->R^o}].
Variable f:G->W.
Hypothesis hF:is_analytic_finite_coefficient_map e f.

(** Source for [finite_analytic_coefficient_zero_jets]: supporting
    exact original coefficient/derivative connection for Federer
    3.4.8(5), p. 328. All finite coefficients vanish exactly when
    the actual derivatives below l vanish; the existing symmetric
    monomial expansion supplies the reverse determination. *)
Theorem finite_analytic_coefficient_zero_jets (z:G):
  f z = 0 <->analytic_germ_jets_vanish_below l z.
Proof.
split.
- move=>hZero k hk.
  have [phi [hPhi _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX a z.
  have hMonomial (b:symmetric_indices n k):phi k (symmetric_monomial_tuple e b) = 0.
    pose j:finite_jet_degree_indices n l:=
      existT (fun h:'I_l=>symmetric_indices n (val h)) (Ordinal hk) b.
    have hJ:f z j = 0.
      have hh:=congr1 (fun v:W=>v j) hZero.
      change (f z j = (0:W) j) in hh.
      by move:hh;rewrite ffunE.
    have hCoefficient:
        ((symmetric_multi_factorial (symmetric_indices_unbound b))%:R:R)^-1 *
          @ContinuousMultilinear.evaluation R k X R^o NX (fun t=>`|t|)
            hNX (@scalar_absolute_value_norm R) (finite_jet_monomial_arguments e j)
            (@AnalyticGermJets.value R X NX hNX a k z) = 0.
      have hh:=hF z j;rewrite hJ in hh;exact:esym hh.
    have hFactor:=@symmetric_multi_factorial_nonzero R (@pchar_num R) n
      (symmetric_indices_unbound b).
    have hInverse:((symmetric_multi_factorial (symmetric_indices_unbound b))%:R:R)^-1!=0.
      by rewrite invr_eq0.
    have hValue:
        @ContinuousMultilinear.evaluation R k X R^o NX (fun t=>`|t|)
          hNX (@scalar_absolute_value_norm R) (finite_jet_monomial_arguments e j)
          (@AnalyticGermJets.value R X NX hNX a k z) = 0.
      apply:(mulfI hInverse);by rewrite mulr0.
    rewrite hPhi;exact:hValue.
  have hForm:phi k = 0.
    apply:sform_ext=>t;rewrite sform_zeroE
      (@symmetric_form_coordinate_expansion R (@pchar_num R) X R^o n e he k (phi k) t).
    apply:big1=>b _;by rewrite hMonomial !scaler0.
  apply:(continuous_multilinear_extensional (@ContinuousMultilinear.laws R k X R^o NX
    (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)))=>u.
  rewrite linear0.
  have hh:=hPhi k [tuple u i | i<k].
  rewrite hForm sform_zeroE in hh.
  have hTuple:[ffun i=>tnth [tuple u j | j<k] i] = u.
    by apply/ffunP=>i;rewrite ffunE tnth_mktuple.
  rewrite hTuple in hh;exact:esym hh.
- move=>hJets;apply/ffunP=>j;rewrite hF ffunE
    (hJets (tag j) (ltn_ord (tag j))) linear0 mulr0.
  reflexivity.
Qed.

(** Source for [finite_analytic_coefficient_power_kernel]: supporting
    exact original finite-jet quotient connection for Federer
    3.4.8(5), p. 328. The kernel is the lth power of the actual
    centre-vanishing ideal, including l=0 and zero source dimension. *)
Theorem finite_analytic_coefficient_power_kernel (z:G):
  f z = 0 <->@CommutativeIdealPowers.value G
    (@AnalyticVanishingIdeal.value R X NX hNX a) l z.
Proof.
rewrite (@finite_analytic_vanishing_power_jet_equivalence R X NX hNX a n e he l z).
exact:finite_analytic_coefficient_zero_jets.
Qed.
End Kernel.
