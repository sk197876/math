(** Federer (1969), 4.1.1, p. 346: test
    differentiation indexed by alpha is exactly
    the D^alpha of 3.1.11, p. 223. The
    proof reuses the original ordered-to-multiindex
    derivative theorem and the Chapter 1 exponent word. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  GrassmannAbbreviations FiniteCoordinates SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials
  SymmetricMonomialTuples SymmetricExponentWords NormHigherSymmetricFormUP NormHigherMultiPartialUP
  NormHigherCoordinatePartials NormIteratedPartial NormIteratedDirectionalLaws
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation
  DistributionIteratedDerivative TestIteratedDerivativeIdentification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section TestMultiindexIdentification.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Variable Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:X->Prop.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ez := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation value := (smooth_test_value hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation Q := (@distribution_test_iterated_derivative R X Y NX NY hNX hNY U hU E ev hE D hD).

(** Source for [test_multiindex_derivative_graph]: the
    actual repeated test operator has the exact
    original multiindex derivative graph, supporting
    TD^alpha in Federer 4.1.1, p. 346. *)
Theorem test_multiindex_derivative_graph k (alpha:symmetric_indices n k) f x:
  U x ->has_norm_multi_partial NX ez ZN U (value f) alpha x
    (value (Q (symmetric_monomial_tuple (@coordinate_basis R n) alpha) f) x).
Proof.
move=>hx.
pose nu:=symmetric_monomial_word (@idfun 'I_n) (symmetric_indices_unbound alpha).
have hSize:size nu=k:=eqP (symmetric_monomial_tuple_size (@idfun 'I_n) alpha).
have hCount i:count_mem i nu=symmetric_indices_unbound alpha i.
  have h:=congr1 (fun a:symmetric_multi_index n=>a i) (symmetric_exponent_word_count_monomial (symmetric_indices_unbound alpha)).
  by rewrite /symmetric_exponent_word_count ffunE in h.
have hExact:=@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD k (inc f) x hx.
have [phi hPhi]:=@norm_higher_differential_form_exists R X Y NX NY hNX hNY Z ez ZN hZ
  U (value f) k x (@D k x (inc f)) hExact.
have [y [hMulti hOrdered]]:=@norm_multi_partial_ordered_formula R n Y NX NY hNX hNY Z ez ZN hZ
  U (value f) k nu alpha x phi hSize hCount hPhi.
have hDirection:=(@norm_iterated_partial_graph R n Y NY hNY U (value f) nu x y).1 hOrdered.
have hMap:[seq (@coordinate_basis R n) i|i<-nu]=
    (symmetric_monomial_tuple (@coordinate_basis R n) alpha:seq X).
  by rewrite /nu symmetric_monomial_word_map /symmetric_monomial_tuple /=.
rewrite hMap in hDirection.
have hActual:=@test_iterated_derivative_graph R X Y NX NY hNX hNY U hU E ev hE D hD
  (symmetric_monomial_tuple (@coordinate_basis R n) alpha) f x hx.
have hSame:=norm_iterated_directional_unique hNY hDirection hActual.
by rewrite -hSame.
Qed.
End TestMultiindexIdentification.
