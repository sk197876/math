(** Federer (1969), 4.1.8, p. 360: each
    higher test-form differential is a finite bounded linear
    combination of the original multiindex test derivatives.
    This supporting statement reuses the complete reconstruction
    of 3.1.11, p. 223, and its actual-test
    identification from 4.1.1, p. 346. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms
  CurrentSpaces ContinuousMultilinearSealed SmoothFunctionDerivativesUP SmoothTestSpaces
  SymmetricMultiIndices SymmetricMonomials SymmetricMonomialTuples NormHigherCoordinateReconstruction
  DistributionIteratedDerivative TestMultiindexDerivativeIdentification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentTestJetReconstruction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n d:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation F := (A_m X R^o d).
Local Notation NF := (@current_form_comass R h2 n d).
Local Notation hNF := (@current_form_comass_real_norm R h2 n d).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (@current_smooth_space R h2 n U hU d).
Local Notation ev := (@current_smooth_value R h2 n U hU d).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU d).
Local Notation D := (@current_smooth_derivatives R h2 n U hU d).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU d).
Local Notation DT := (@current_test_space R h2 n U hU d).
Local Notation value := (fun f=>@current_test_value R h2 n U hU d f).
Local Notation J := (fun k=>@ContinuousMultilinear.space R k X F NX NF hNX hNF).
Local Notation ez := (fun k=>@ContinuousMultilinear.evaluation R k X F NX NF hNX hNF).
Local Notation JN := (fun k=>@ContinuousMultilinear.norm R k X F NX NF hNX hNF).
Local Notation hJ := (fun k=>@ContinuousMultilinear.laws R k X F NX NF hNX hNF).
Local Notation Iter := (@distribution_test_iterated_derivative R X F NX NF hNX hNF
  U hU E ev hE D hD).

(** Source for [current_test_jet_reconstruction]: fixed bounded
    linear maps reconstruct every actual order-k test-form
    differential from its original coordinate multiindex derivatives,
    supporting Federer 4.1.8, p. 360. Empty coordinate
    families, derivative order zero and dimension zero remain included. *)
Theorem current_test_jet_reconstruction k:
  exists iota:symmetric_indices n k->Hom F (J k),
    (forall alpha,norm_bounded_linear NF (@JN k) (iota alpha)) /\
    forall (f:DT) x,U x->@D k x (smooth_test_inclusion hE f)=
      \sum_(alpha:symmetric_indices n k) iota alpha
        (value (Iter (symmetric_monomial_tuple (@coordinate_basis R n) alpha) f) x).
Proof.
have[iota [hBound hReconstruct]]:=@norm_higher_coordinate_reconstruction_exists R n F NF hNF
  J ez JN hJ k.
exists iota;split;first exact:hBound.
move=>f x hx.
have hActual:=@smooth_derivative_exact R X F NX NF hNX hNF U E ev D hD k
  (smooth_test_inclusion hE f) x hx.
exact:(@hReconstruct U (value f) x (@D k x (smooth_test_inclusion hE f))
  (fun alpha=>value (Iter (symmetric_monomial_tuple (@coordinate_basis R n) alpha) f) x)
  hActual (fun alpha=>@test_multiindex_derivative_graph R n F NX NF hNX hNF U hU E ev hE
    D hD k alpha f x hx)).
Qed.
End CurrentTestJetReconstruction.
