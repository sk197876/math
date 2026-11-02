(** Federer (1969), 1.6.6, pp. 26-27: alpha_1,...,alpha_n together with
    their conjugates form a complex basis of all real one-forms with complex
    values. The proof uses the paired real basis and explicitly solves for
    the two coefficients in each pair. Source context are recorded in
    ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates ScalarRestriction
  ComplexScalarUP ComplexScalarSealed ComplexScalarLaws ComplexCharacteristic
  ComplexPairCoordinates ComplexRealBasis ComplexAlternatingForms ComplexValuedForms
  ComplexFormSubspace ComplexFormConjugation ComplexCoefficientAlgebra
  FormBasisValues OneFormIdentification FiniteBasisCriterion FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

Section OneForms.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).
Local Notation CR := (complex_real_algebra R).
Local Notation CF := (complex_valued_form embed VR C^o 1).
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation J := (Finite.clone ('I_n + 'I_n)%type _).

(** Source for [complex_basis_one_form]: Federer 1.6.6,
    p. 26, the dual complex basis alpha_j. Its inclusion among
    complex-valued real one-forms. *)
Definition complex_basis_one_form j : CF :=
  complex_form_inclusion embed (one_form (dual_basis he j)).

(** Source for [mixed_basis_one_form]: Federer 1.6.6, p. 27,
    the mixed basis in degree one. The left copy indexes alpha_j;
    the right copy indexes its complex conjugate. *)
Definition mixed_basis_one_form (j : J) : CF :=
  match j with
  | inl i => complex_basis_one_form i
  | inr i => real_as_complex_valued
      (conjugate_form (complex_valued_as_real (complex_basis_one_form i)))
  end.

(** Source for [complex_basis_one_formE]: Federer 1.6.6,
    p. 26, dual complex basis. Its value is the complex coordinate. *)
Lemma complex_basis_one_formE j v : complex_basis_one_form j [tuple v] = dual_basis he j v.
Proof. exact: one_formE. Qed.

(** Source for [mixed_basis_real_values]: Federer 1.6.6,
    pp. 26-27, mixed one-form basis. Both members of a conjugate pair
    have the same Kronecker values on the original basis. *)
Lemma mixed_basis_real_values j k : mixed_basis_one_form j [tuple e k] =
  match j with inl i => if i == k then 1 else 0 | inr i => if i == k then 1 else 0 end.
Proof.
case: j => j.
- by rewrite /mixed_basis_one_form complex_basis_one_formE dual_basisE eq_sym.
- change (conjugate_form (complex_valued_as_real (complex_basis_one_form j)) [tuple e k] =
    if j == k then 1 else 0).
  rewrite conjugate_formE.
  change (conjugate (complex_basis_one_form j [tuple e k]) = if j == k then 1 else 0).
  rewrite complex_basis_one_formE dual_basisE (eq_sym j k).
  case: (k == j).
  + by rewrite -(rmorph1 embed) conjugate_real.
  + by rewrite -(rmorph0 embed) conjugate_real.
Qed.

(** Source for [mixed_basis_imaginary_values]: Federer 1.6.6,
    pp. 26-27, mixed one-form basis. The unbarred and barred forms
    have opposite imaginary values on i e_k. *)
Lemma mixed_basis_imaginary_values j k : mixed_basis_one_form j [tuple ii *: e k] =
  match j with
  | inl i => ii * (if i == k then 1 else 0)
  | inr i => - (ii * (if i == k then 1 else 0))
  end.
Proof.
case: j => j.
- rewrite /mixed_basis_one_form complex_basis_one_formE realified_dual_imaginary dual_basisE.
  by rewrite eq_sym.
- change (conjugate_form (complex_valued_as_real (complex_basis_one_form j)) [tuple ii *: e k] =
    -(ii * (if j == k then 1 else 0))).
  rewrite conjugate_formE.
  change (conjugate (complex_basis_one_form j [tuple ii *: e k]) =
    -(ii * (if j == k then 1 else 0))).
  rewrite complex_basis_one_formE realified_dual_imaginary conjugate_i_mul.
  have h := mixed_basis_real_values (inr j : J) k.
  change (conjugate_form (complex_valued_as_real (complex_basis_one_form j)) [tuple e k] = if j == k then 1 else 0) in h.
  rewrite conjugate_formE in h.
  change (conjugate (complex_basis_one_form j [tuple e k]) = if j == k then 1 else 0) in h.
  by rewrite complex_basis_one_formE in h; rewrite h.
Qed.

(** Source for [mixed_one_form_coordinates]: Federer 1.6.6,
    p. 27, mixed one-form basis. Explicit coefficients (u-i v)/2
    and (u+i v)/2, where u and v are the values on e_j and i e_j. *)
Definition mixed_one_form_coordinates (j : J) (a : CF) : C :=
  match j with
  | inl i => holomorphic_coefficient (a [tuple e i]) (a [tuple ii *: e i])
  | inr i => antiholomorphic_coefficient (a [tuple e i]) (a [tuple ii *: e i])
  end.

(** Source for [mixed_one_form_coordinates_linear]: Federer
    1.6.6, p. 27, mixed one-form basis. Each coordinate is C-linear. *)
Lemma mixed_one_form_coordinates_linear j : scalar (mixed_one_form_coordinates j).
Proof.
case: j=> j; move=> c a b; rewrite /mixed_one_form_coordinates
  /holomorphic_coefficient /antiholomorphic_coefficient
  !complex_valued_form_addE !complex_valued_form_scaleE.
- change ((c * a [tuple e j] + b [tuple e j] -
    ii * (c * a [tuple ii *: e j] + b [tuple ii *: e j])) / (1+1) =
    c * ((a [tuple e j] - ii * a [tuple ii *: e j]) / (1+1)) +
    (b [tuple e j] - ii * b [tuple ii *: e j]) / (1+1)).
  by rewrite mulrDr [ii * (c * _)]mulrCA opprD addrACA
    -mulrBr mulrDl mulrA.
- change ((c * a [tuple e j] + b [tuple e j] +
    ii * (c * a [tuple ii *: e j] + b [tuple ii *: e j])) / (1+1) =
    c * ((a [tuple e j] + ii * a [tuple ii *: e j]) / (1+1)) +
    (b [tuple e j] + ii * b [tuple ii *: e j]) / (1+1)).
  by rewrite mulrDr [ii * (c * _)]mulrCA addrACA -mulrDr mulrDl mulrA.
Qed.
HB.instance Definition _ j := GRing.isLinear.Build C CF C^o *:%R
  (mixed_one_form_coordinates j) (mixed_one_form_coordinates_linear j).

(** Source for [mixed_one_form_coordinates_basis]: Federer 1.6.6,
    p. 27, mixed basis. The explicit coordinates are biorthogonal
    to the unbarred and barred one-forms. *)
Lemma mixed_one_form_coordinates_basis i j :
  mixed_one_form_coordinates i (mixed_basis_one_form j) =
    if i == j then 1 else 0.
Proof.
have hp u : holomorphic_coefficient u (ii*u) = u.
  by have h := holomorphic_coefficient_pair u (0:C); rewrite addr0 subr0 in h.
have hq u : antiholomorphic_coefficient u (ii*u) = 0.
  by have h := antiholomorphic_coefficient_pair u (0:C); rewrite addr0 subr0 in h.
have hr u : holomorphic_coefficient u (- (ii*u)) = 0.
  by have h := holomorphic_coefficient_pair (0:C) u; rewrite add0r sub0r mulrN in h.
have hs u : antiholomorphic_coefficient u (- (ii*u)) = u.
  by have h := antiholomorphic_coefficient_pair (0:C) u; rewrite add0r sub0r mulrN in h.
case: i => i; case: j => j;
  rewrite /mixed_one_form_coordinates mixed_basis_real_values mixed_basis_imaginary_values /=.
- by rewrite hp eq_sym.
- exact: hr.
- exact: hq.
- by rewrite hs eq_sym.
Qed.

(** Source for [mixed_one_form_values_ext]: Federer 1.6.6,
    pp. 26-27, paired real basis. A real one-form is determined
    by its values on e_j and i e_j. *)
Lemma mixed_one_form_values_ext (a b : CF) :
  (forall j, a [tuple e j] = b [tuple e j]) ->
  (forall j, a [tuple ii *: e j] = b [tuple ii *: e j]) -> a = b.
Proof.
move=> hr hi; apply: (can_inj (@complex_valued_realK R C embed VR C^o 1)).
apply: (can_inj (@one_homK R VR (restricted_space embed C^o))); apply: hom_ext => v.
apply: (basis_linear_ext (realified_basisP he)
  (hom_as_linear (one_hom (complex_valued_as_real a)))
  (hom_as_linear (one_hom (complex_valued_as_real b)))) v.
move=> [j t].
change (one_hom (complex_valued_as_real a) (realified_basis e (j,t)) =
  one_hom (complex_valued_as_real b) (realified_basis e (j,t))).
rewrite !one_homE; case: t; [exact: hi | exact: hr].
Qed.

(** Source for [mixed_one_form_sum_real]: Federer 1.6.6,
    p. 27, mixed basis. Evaluation of an arbitrary combination
    on an original complex basis vector. *)
Lemma mixed_one_form_sum_real (c : J -> C) k :
  (\sum_j c j *: mixed_basis_one_form j) [tuple e k] = c (inl k) + c (inr k).
Proof.
change (@complex_form_evaluate R C embed VR 1 [tuple e k] (\sum_j c j *: mixed_basis_one_form j) = c (inl k) + c (inr k)).
rewrite linear_sum.
under eq_bigr do rewrite linearZ.
change ((\sum_j c j * mixed_basis_one_form j [tuple e k]) = c (inl k) + c (inr k)).
under eq_bigr do rewrite mixed_basis_real_values.
rewrite big_sumType /=.
congr (_ + _); rewrite (bigD1 k) //= eqxx mulr1;
  rewrite [X in _ + X]big1 ?addr0 // => j hj; by rewrite (negbTE hj) mulr0.
Qed.

(** Source for [mixed_one_form_sum_imaginary]: Federer 1.6.6,
    p. 27, mixed basis. Evaluation of an arbitrary combination
    on the imaginary multiple of a basis vector. *)
Lemma mixed_one_form_sum_imaginary (c : J -> C) k :
  (\sum_j c j *: mixed_basis_one_form j) [tuple ii *: e k] =
    ii * (c (inl k) - c (inr k)).
Proof.
change (@complex_form_evaluate R C embed VR 1 [tuple ii *: e k] (\sum_j c j *: mixed_basis_one_form j) = ii * (c (inl k) - c (inr k))).
rewrite linear_sum.
under eq_bigr do rewrite linearZ.
change ((\sum_j c j * mixed_basis_one_form j [tuple ii *: e k]) =
  ii * (c (inl k) - c (inr k))).
under eq_bigr do rewrite mixed_basis_imaginary_values.
rewrite big_sumType /= mulrBr.
congr (_ + _).
- rewrite (bigD1 k) //= eqxx mulr1.
  have hz : (\sum_(j | j != k) c (inl j) * (ii * (if j == k then 1 else 0))) = 0.
    apply: big1 => j hj; by rewrite (negbTE hj) !mulr0.
  by rewrite hz addr0 mulrC.
- rewrite (bigD1 k) //= eqxx mulr1.
  have hz : (\sum_(j | j != k) c (inr j) * (- (ii * (if j == k then 1 else 0)))) = 0.
    apply: big1 => j hj; by rewrite (negbTE hj) mulr0 oppr0 mulr0.
  by rewrite hz addr0 mulrN mulrC.
Qed.

(** Source for [mixed_one_form_basisP]: Federer 1.6.6,
    p. 27, the stated mixed basis in degree one. Both independence
    and spanning hold over C, including the zero-dimensional case. *)
Theorem mixed_one_form_basisP : is_basis mixed_basis_one_form.
Proof.
apply: finite_basis_criterion.
- apply: (@finite_independent_separating C J CF mixed_basis_one_form
    (fun j => GRing.Linear.clone C CF C^o *:%R (mixed_one_form_coordinates j) _)).
  exact: mixed_one_form_coordinates_basis.
- move=> a; exists (fun j => mixed_one_form_coordinates j a).
  apply: mixed_one_form_values_ext => j.
  + by rewrite mixed_one_form_sum_real /mixed_one_form_coordinates complex_pair_coordinate_sum.
  + by rewrite mixed_one_form_sum_imaginary /mixed_one_form_coordinates complex_pair_coordinate_difference.
Qed.
End OneForms.
