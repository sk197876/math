(** Federer (1969), 1.9.2, p. 42: the zero-dimensional boundary of the
    monomial basis assertion. The algebra is the scalar field in degree zero
    and vanishes in positive degrees. The proofs use only the abstract
    interface. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import TensorUP FreeVector LinearBasis Bilinear AlgebraUP
  GradedAlgebra GradedBasis GradedComponents TensorPowers SymmetricAlgebra SymmetricGrading.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ZeroSpace.
Variable K : fieldType.
Variable V : lmodType K.
Hypothesis hV : forall v : V, v = 0.
Local Notation E := (symmetric_space V).
Local Notation F := (free_vector K (Choice.clone unit _)).

(** Source for [zero_space_symmetric_word]: Federer 1.9.2,
    p. 42, supporting zero-space boundary: every nonempty word
    vanishes, while the empty word remains the unit. *)
Lemma zero_space_symmetric_word s :
  symmetric_word s = if size s == 0 then symmetric_unit V else 0.
Proof.
case: s => [|v s] //=.
by rewrite symmetric_word_cons (hV v) linear0 (bil0l (symmetric_product_bilinear V)).
Qed.

(** Source for [zero_space_symmetric_scalar_reconstruction]: Federer
    1.9.2, p. 42, supporting fact that every symmetric element of
    the zero space is a scalar multiple of the unit. *)
Lemma zero_space_symmetric_scalar_reconstruction x :
  symmetric_scalar V (symmetric_augmentation V x) = x.
Proof.
elim/symmetric_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- rewrite !linearD.
  change (symmetric_scalar V (symmetric_augmentation V x) +
    symmetric_scalar V (symmetric_augmentation V y) = x+y).
  by rewrite hx hy.
- rewrite !linearZ.
  change (a *: symmetric_scalar V (symmetric_augmentation V x) = a *: x).
  by rewrite hx.
rewrite symmetric_augmentation_word zero_space_symmetric_word /symmetric_scalar.
by case: s => [|v s] /=; rewrite /word_degree_zero /= ?scale1r ?scale0r.
Qed.

(** Source for [zero_space_symmetric_power]: Federer 1.9.2, p. 42,
    positive-degree symmetric powers of the zero space vanish *)
Theorem zero_space_symmetric_power m (hm : (0 < m)%N)
    (x : symmetric_power V m) : x = 0.
Proof.
apply: val_inj; rewrite linear0.
apply: (@symmetric_component_induction K V m (fun z => z = 0))
  (component_homogeneous x) => [|z t hz ht|a z hz|s hs] => //.
- by rewrite hz ht add0r.
- by rewrite hz scaler0.
- rewrite zero_space_symmetric_word hs.
  by rewrite eq_sym (ltn_eqF hm).
Qed.

(** Source for [zero_space_symmetric_coordinates]: Federer 1.9.2,
    p. 42, supporting coordinate map for the sole degree-zero
    basis vector, the algebra unit. *)
Definition zero_space_symmetric_coordinates (x : E) : F :=
  (symmetric_augmentation V x : K) *: delta K tt.

(** Source for [zero_space_symmetric_coordinates_linear]: Federer
    1.9.2, p. 42, this scalar coordinate map is linear. *)
Lemma zero_space_symmetric_coordinates_linear : linear zero_space_symmetric_coordinates.
Proof.
move=> a x y; rewrite /zero_space_symmetric_coordinates linearP.
change ((a * (symmetric_augmentation V x : K) + (symmetric_augmentation V y : K)) *: delta K tt =
  a *: ((symmetric_augmentation V x : K) *: delta K tt) +
    (symmetric_augmentation V y : K) *: delta K tt).
by rewrite scalerDl scalerA.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K E F *:%R
  zero_space_symmetric_coordinates zero_space_symmetric_coordinates_linear.

(** Source for [zero_space_symmetric_unit_basis]: Federer 1.9.2,
    p. 42, supporting homogeneous basis of the whole symmetric
    algebra of the zero space: its sole vector is the unit in degree zero. *)
Theorem zero_space_symmetric_unit_basis :
  is_graded_basis (symmetric_grading V) (fun _ : unit => symmetric_unit V) (fun _ => 0%N).
Proof.
split; last by move=> []; exact: symmetric_unit_homogeneous.
exists (GRing.Linear.clone _ _ _ _ zero_space_symmetric_coordinates _); split.
- apply: free_induction => [|x y hx hy|a x hx|[]].
  + by rewrite !linear0.
  + by rewrite !linearD hx hy.
  + by rewrite !linearZ hx.
  + rewrite basis_synthesisE.
    change ((symmetric_augmentation V (symmetric_unit V) : K) *: delta K tt = delta K tt).
    by rewrite symmetric_augmentation_unit scale1r.
- move=> x.
  change (basis_synthesis (fun _ : unit => symmetric_unit V)
    ((symmetric_augmentation V x : K) *: delta K tt) = x).
  rewrite linearZ basis_synthesisE.
  exact: zero_space_symmetric_scalar_reconstruction.
Qed.
End ZeroSpace.
