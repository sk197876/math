(** Federer (1969), 1.10.2, p. 45: the dual monomial basis. These supporting
    coordinate maps will identify the actual products of one-forms. They are
    not substituted for that product assertion. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import TensorUP Bilinear GradedAlgebra Hom HomogeneousHom BoundedHom
  HomogeneousSum LinearBasis BasisInterpolation SymmetricAlgebra SymmetricGrading
  SymmetricMultiIndices SymmetricMonomials SymmetricMonomialBasis
  SymmetricDividedMonomials SymmetricForms SymmetricFormIsomorphism SymmetricFormSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Coordinates.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation E := (symmetric_space V).
Local Notation G := (symmetric_grading V).
Local Notation hb := (proj1 (symmetric_monomials_basis he)).

(** Source for [symmetric_monomial_coordinate]: Federer 1.10.2,
    p. 45, supporting coordinate functional for the ordinary monomial
    e^alpha in the basis supplied by 1.9.2. *)
Definition symmetric_monomial_coordinate (a : symmetric_multi_index n) : Hom E K^o :=
  hom_of_linear (@basis_interpolation K (symmetric_multi_index n) E K^o (symmetric_monomial e) hb (fun b => if b == a then (1 : K) else 0)).

(** Source for [symmetric_monomial_coordinateE]: Federer 1.10.2,
    p. 45, the coordinate functional equals one on its own monomial
    and zero on every other monomial. *)
Lemma symmetric_monomial_coordinateE a b :
  symmetric_monomial_coordinate a (symmetric_monomial e b) = if b == a then 1 else 0.
Proof. by rewrite /symmetric_monomial_coordinate hom_of_linearE basis_interpolationE. Qed.

(** Source for [symmetric_monomial_coordinate_projection]: Federer
    1.10.2, p. 45, supporting degree calculation: a monomial coordinate
    only sees the homogeneous component of its total degree. *)
Lemma symmetric_monomial_coordinate_projection a x :
  symmetric_monomial_coordinate a (symmetric_degree (symmetric_multi_degree a) x) =
    symmetric_monomial_coordinate a x.
Proof.
apply: (basis_linear_ext hb
  (linear_comp (hom_as_linear (symmetric_monomial_coordinate a))
    (symmetric_degree (symmetric_multi_degree a)))
  (hom_as_linear (symmetric_monomial_coordinate a))) x=> b.
change (symmetric_monomial_coordinate a
  (symmetric_degree (symmetric_multi_degree a) (symmetric_monomial e b)) =
  symmetric_monomial_coordinate a (symmetric_monomial e b)).
rewrite /symmetric_degree (grade_homogeneous _ (symmetric_monomial_homogeneous e b)).
case: ifP=> hd; first by [].
rewrite linear0 symmetric_monomial_coordinateE.
case: ifP=> [/eqP hba|//].
by move: hd; rewrite hba eqxx.
Qed.

(** Source for [symmetric_monomial_coordinate_degree]: Federer
    1.10.2, p. 45, the coordinate map vanishes on every other degree. *)
Lemma symmetric_monomial_coordinate_degree a :
  hom_degree G (symmetric_multi_degree a) (symmetric_monomial_coordinate a).
Proof.
move=> k x hk hx.
rewrite -(symmetric_monomial_coordinate_projection a x) /symmetric_degree
  (grade_homogeneous _ hx) eq_sym (negbTE hk).
exact: linear0.
Qed.

(** Source for [symmetric_divided_coordinate]: Federer 1.10.2,
    p. 45, supporting functional dual to the divided monomial
    e^alpha/alpha!: multiply the ordinary coordinate by alpha!. *)
Definition symmetric_divided_coordinate a : Hom E K^o :=
  (symmetric_multi_factorial a)%:R *: symmetric_monomial_coordinate a.

(** Source for [symmetric_divided_coordinate_degree]: Federer
    1.10.2, p. 45, this scalar rescaling preserves degree support. *)
Lemma symmetric_divided_coordinate_degree a :
  hom_degree G (symmetric_multi_degree a) (symmetric_divided_coordinate a).
Proof.
move=> k x hk hx; rewrite /symmetric_divided_coordinate hom_scaleE.
by rewrite (symmetric_monomial_coordinate_degree hk hx) scaler0.
Qed.

(** Source for [symmetric_coordinate_homogeneous]: Federer 1.10.2,
    p. 45, package the normalized dual functional as a homogeneous map. *)
Definition symmetric_coordinate_homogeneous a : Hom_m K^o G (symmetric_multi_degree a) :=
  @HomogeneousHom K E K^o G (symmetric_multi_degree a) (symmetric_divided_coordinate a)
    (introT (asboolP _) (@symmetric_divided_coordinate_degree a)).

(** Source for [symmetric_coordinate_form]: Federer 1.10.2,
    p. 45, the symmetric form corresponding to the normalized coordinate. *)
Definition symmetric_coordinate_form a : S_m V K^o (symmetric_multi_degree a) :=
  homogeneous_sform (symmetric_coordinate_homogeneous a).

(** Source for [symmetric_coordinate_full_form]: Federer 1.10.2,
    p. 45, regard that coordinate form in the full graded space. *)
Definition symmetric_coordinate_full_form a : S_star V K^o :=
  homogeneous_include (symmetric_coordinate_homogeneous a).

(** Source for [symmetric_coordinate_full_formE]: Federer 1.10.2,
    p. 45, the full form evaluates as its normalized coordinate map. *)
Lemma symmetric_coordinate_full_formE a x :
  symmetric_coordinate_full_form a x = (symmetric_multi_factorial a)%:R *
    symmetric_monomial_coordinate a x.
Proof. by []. Qed.

(** Source for [symmetric_coordinate_full_form_graded]: Federer
    1.10.2, p. 45, its only nonzero component has total degree |alpha|. *)
Lemma symmetric_coordinate_full_form_graded a :
  homogeneous (S_star_grading V K^o) (symmetric_multi_degree a)
    (symmetric_coordinate_full_form a).
Proof.
change (finite_hom_grade (symmetric_multi_degree a)
  (homogeneous_include (symmetric_coordinate_homogeneous a)) =
  homogeneous_include (symmetric_coordinate_homogeneous a)).
by rewrite homogeneous_include_grade eqxx.
Qed.

(** Source for [symmetric_coordinate_divided_monomial]: Federer
    1.10.2, p. 45, supporting normalized Kronecker pairing. Characteristic
    zero ensures that every multiindex factorial is nonzero. *)
Lemma symmetric_coordinate_divided_monomial (h0 : [pchar K] =i pred0) a b :
  symmetric_coordinate_full_form a (symmetric_divided_monomial e b) =
    if b == a then 1 else 0.
Proof.
rewrite symmetric_coordinate_full_formE /symmetric_divided_monomial linearZ.
change ((symmetric_multi_factorial a)%:R *
  ((symmetric_multi_factorial b)%:R^-1 * symmetric_monomial_coordinate a (symmetric_monomial e b)) =
  if b == a then 1 else 0).
rewrite symmetric_monomial_coordinateE.
case: ifP=> [/eqP ->|_]; last by rewrite mulr0 mulr0.
by rewrite mulr1 mulfV //; exact: (@symmetric_multi_factorial_nonzero K h0).
Qed.
End Coordinates.
