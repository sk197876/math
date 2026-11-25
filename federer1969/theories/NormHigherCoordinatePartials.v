(** Federer (1969), 3.1.11, p. 223: ordered partial
    derivatives and their multiindex identification. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom HomogeneousHom RealNormUP PartialFunctionUP
  GrassmannAbbreviations FiniteCoordinates SymmetricAlgebra SymmetricForms
  SymmetricFormExtension SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials
  SymmetricExponentWords SymmetricWordFibres ContinuousMultilinearUP
  NormHigherSymmetricFormUP NormHigherMultiPartialUP NormIteratedPartial
  NormHigherFormIteratedDirections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CoordinatePartials.
Variable R : realType.
Variable n : nat.
Variable Y : lmodType R.
Variables (NX : R_n R n->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R n}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i).
Variables (A : R_n R n->Prop) (f : R_n R n->Y).

(** Source for [norm_higher_coordinate_partial_formula]:
    D_nu f(a)=D^k f(a)(e_nu_k,...,e_nu_1), the
    displayed formula in Federer 3.1.11, p. 223. The
    recursive partial derivative is the sealed exact graph. *)
Theorem norm_higher_coordinate_partial_formula k (nu : seq 'I_n) a
    (phi : S_m (R_n R n) Y k) :
  size nu=k -> is_norm_higher_differential_form NX ev ZN A f k a phi ->
  partial_function_graph (norm_iterated_partial hNY A f nu) a
    (sform_homogeneous phi
      (symmetric_word (rev [seq (@coordinate_basis R n) i | i <- nu]))).
Proof.
move=>hsize hphi.
apply: (@norm_iterated_partial_graph R n Y NY hNY A f nu a
  (sform_homogeneous phi
    (symmetric_word (rev [seq (@coordinate_basis R n) i | i <- nu])))).2.
apply: (@norm_higher_form_iterated_directions R (R_n R n) Y NX NY hNX hNY
  Z ev ZN hZ A f k [seq (@coordinate_basis R n) i | i <- nu] a phi) => //.
by rewrite size_map hsize.
Qed.

(** Source for [norm_multi_partial_ordered_formula]: D^alpha
    f(a)=D_nu f(a) when alpha_i counts the occurrences of
    i in nu, Federer 3.1.11, p. 223. The equality
    follows by the already proved symmetry of the higher differential;
    no separate commutation hypothesis for partial derivatives is added. *)
Theorem norm_multi_partial_ordered_formula k (nu : seq 'I_n)
    (alpha : symmetric_indices n k) a (phi : S_m (R_n R n) Y k) :
  size nu=k ->
  (forall i, count_mem i nu=symmetric_indices_unbound alpha i) ->
  is_norm_higher_differential_form NX ev ZN A f k a phi ->
  exists y,
    has_norm_multi_partial NX ev ZN A f alpha a y /\
    partial_function_graph (norm_iterated_partial hNY A f nu) a y.
Proof.
move=>hsize hcount hphi.
exists (sform_homogeneous phi
  (symmetric_monomial (@coordinate_basis R n) (symmetric_indices_unbound alpha))).
split; first exact: norm_multi_partial_form_evaluation hphi.
have hh := norm_higher_coordinate_partial_formula hsize hphi.
have he : symmetric_exponent_word_count (rev nu)=symmetric_indices_unbound alpha.
  apply/ffunP=>i; rewrite /symmetric_exponent_word_count ffunE count_rev.
  exact: hcount.
by rewrite -map_rev symmetric_word_occurrence_monomial he in hh.
Qed.
End CoordinatePartials.
