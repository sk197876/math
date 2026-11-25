(** Federer (1969), 4.1.7, pp. 355–357: the
    finite covector space satisfies the separable Banach
    hypotheses of 4.1.5. Existing finite-basis and
    normed-space theorems include every exterior degree. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP CompleteMetricUP
  LinearBasis ExteriorGrading ExteriorIndices FiniteExteriorPowers FiniteDualDimension
  AlternatingForms GrassmannAbbreviations FiniteCoordinates CurrentCoefficientNorms
  FiniteNormMetricPolish VectorDaniellHypotheses NormFiniteLinearBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCoefficientCompleteness.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation V := (R_n R n).
Local Notation Y := (A_m V R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).

(** Source for [current_form_finite_basis]: finite
    dimensionality of the original covectors used in
    Federer 4.1.7, p. 357, from 1.4.3, p. 19. *)
Lemma current_form_finite_basis:
  exists k,exists b:'I_k->Y,is_basis b.
Proof.
pose I:finType:=Finite.clone (Lambda n m) _.
pose e:I->exterior_power V m:=fun lambda=>e_lambda (@coordinate_basis R n) (val lambda).
have he:is_basis e:=@finite_e_lambda_basis R n V (@coordinate_basis R n)
  (@coordinate_basisP R n) h2 m.
pose a:I->Y:=@alternating_coordinate_basis R V m I e he.
have ha:is_basis a:=@alternating_coordinate_basisP R V m I e he.
exists #|I|,(fun i=>a (enum_val i)).
exact:(@basis_reindex R (Choice.clone I _) (Choice.clone 'I_(#|I|) _) Y a ha
  enum_rank enum_val (@enum_rankK I) (@enum_valK I)).
Qed.

(** Source for [current_form_complete]: the original
    comass norm is complete, discharging the Banach
    premise used in Federer 4.1.7, p. 357. *)
Theorem current_form_complete:is_complete_metric_space (real_norm_metric_space hNY).
Proof.
have [k [b hb]]:=current_form_finite_basis.
exact:(@finite_norm_metric_complete R Y NY hNY k b hb).
Qed.

(** Source for [current_form_separable]: the original
    covector space is separable, discharging the
    corresponding premise of Federer 4.1.7, p. 357. *)
Theorem current_form_separable:is_separable_normed_space hNY.
Proof.
have [k [b hb]]:=current_form_finite_basis.
exact:(@finite_norm_metric_separable R Y NY hNY k b hb).
Qed.

(** Source for [current_form_linear_bounded]: linear
    coefficient operations on the finite covectors are
    bounded, supporting Federer 4.1.7, pp. 355–356,
    by the earlier finite norm-equivalence theorem. *)
Theorem current_form_linear_bounded (W:lmodType R) (NW:W->R)
    (hNW:is_real_norm NW) (L:Hom Y W):norm_bounded_linear NY NW L.
Proof.
have [k [b hb]]:=current_form_finite_basis.
exact:(@norm_finite_linear_bounded R Y W NY NW hNY hNW k b hb L).
Qed.
End CurrentCoefficientCompleteness.
