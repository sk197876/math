(** Private existence witness for the endomorphism algebra
    of Federer (1969), 3.1.11, p. 220. Composition
    and identity are represented using the already sealed
    continuous-operator space; the new choices stay private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import TensorUP Hom AlgebraUP RealNormUP NormDifferentialUP
  NormDifferentialLinear ContinuousOperatorUP ContinuousOperatorSealed
  ContinuousOperatorAlgebraUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Witness.
Variable R : realType.
Variable X : lmodType R.
Variable NX : X->R.
Hypothesis hNX : is_real_norm NX.
Local Notation Z := (@ContinuousOperator.space R X X NX NX hNX hNX).
Local Notation J := (@ContinuousOperator.evaluation R X X NX NX hNX hNX).
Local Notation ZN := (@ContinuousOperator.norm R X X NX NX hNX hNX).
Local Notation hZ := (@ContinuousOperator.laws R X X NX NX hNX hNX).

(** Source for [operator_algebra_unit_exists]: the identity
    operator belongs to E, Federer 3.1.11, p. 220.
    Its bound is one even when the source is zero dimensional. *)
Lemma operator_algebra_unit_exists :
  exists u : Z, J u=hom_of_linear (linear_id X).
Proof.
apply: (continuous_operator_surjective hZ).
exists 1; split; first exact: ler01.
by move=> x; rewrite hom_of_linearE /= mul1r.
Qed.

(** Source for [operator_algebra_product_exists]: the
    composition of two members belongs to E, supporting
    Federer 3.1.11, p. 220. *)
Lemma operator_algebra_product_exists (u v : Z) :
  exists w : Z, J w=hom_comp (J u) (J v).
Proof.
apply: (continuous_operator_surjective hZ).
exact: norm_bounded_linear_compose (continuous_operator_bounded hZ v)
  (continuous_operator_bounded hZ u).
Qed.

(** Source for [operator_algebra_unit_witness]: private
    identity witness for E, Federer 3.1.11, p. 220. *)
Definition operator_algebra_unit_witness : Z :=
  projT1 (cid operator_algebra_unit_exists).

(** Source for [operator_algebra_product_witness]: private
    composition witness for E, Federer 3.1.11, p. 220. *)
Definition operator_algebra_product_witness (u v : Z) : Z :=
  projT1 (cid (operator_algebra_product_exists u v)).

(** Source for [operator_algebra_unit_witnessE]: evaluation
    of the private identity witness, supporting Federer
    3.1.11, p. 220. *)
Lemma operator_algebra_unit_witnessE :
  J operator_algebra_unit_witness=hom_of_linear (linear_id X).
Proof. exact: projT2 (cid operator_algebra_unit_exists). Qed.

(** Source for [operator_algebra_product_witnessE]: evaluation
    of the private composition witness, supporting Federer
    3.1.11, p. 220. *)
Lemma operator_algebra_product_witnessE u v :
  J (operator_algebra_product_witness u v)=hom_comp (J u) (J v).
Proof. exact: projT2 (cid (operator_algebra_product_exists u v)). Qed.

(** Source for [operator_algebra_product_bilinear]: bilinearity
    of composition, used in Federer 3.1.11, p. 220. *)
Lemma operator_algebra_product_bilinear : bilinear operator_algebra_product_witness.
Proof.
split.
- move=> v c u w; apply: (continuous_operator_injective hZ).
  rewrite operator_algebra_product_witnessE !linearP /= !operator_algebra_product_witnessE.
  exact: hom_precompose_linear.
- move=> u c v w; apply: (continuous_operator_injective hZ).
  rewrite operator_algebra_product_witnessE !linearP /= !operator_algebra_product_witnessE.
  exact: hom_postcompose_linear.
Qed.

(** Source for [operator_algebra_product_associative]:
    associativity of composition in E, supporting the inverse
    series of Federer 3.1.11, p. 220. *)
Lemma operator_algebra_product_associative : associative operator_algebra_product_witness.
Proof.
move=> u v w; apply: (continuous_operator_injective hZ).
rewrite !operator_algebra_product_witnessE.
apply: hom_ext=> x; by rewrite !hom_compE.
Qed.

(** Source for [operator_algebra_unit_left]: the identity
    is a left unit for E, Federer 3.1.11, p. 220. *)
Lemma operator_algebra_unit_left :
  left_id operator_algebra_unit_witness operator_algebra_product_witness.
Proof.
move=> u; apply: (continuous_operator_injective hZ).
rewrite operator_algebra_product_witnessE operator_algebra_unit_witnessE.
apply: hom_ext=> x; by rewrite hom_compE hom_of_linearE.
Qed.

(** Source for [operator_algebra_unit_right]: the identity
    is a right unit for E, Federer 3.1.11, p. 220. *)
Lemma operator_algebra_unit_right :
  right_id operator_algebra_unit_witness operator_algebra_product_witness.
Proof.
move=> u; apply: (continuous_operator_injective hZ).
rewrite operator_algebra_product_witnessE operator_algebra_unit_witnessE.
apply: hom_ext=> x; by rewrite hom_compE hom_of_linearE.
Qed.

(** Source for [continuous_operator_algebra_witness]:
    the private proved algebra witnessing E in Federer
    3.1.11, p. 220. *)
Definition continuous_operator_algebra_witness : algebra R :=
  @Algebra R Z operator_algebra_product_witness operator_algebra_unit_witness
    operator_algebra_product_bilinear operator_algebra_product_associative
    operator_algebra_unit_left operator_algebra_unit_right.

(** Source for [continuous_operator_algebra_witness_laws]:
    all promises for E are proved by the witness,
    Federer 3.1.11, p. 220. *)
Lemma continuous_operator_algebra_witness_laws :
  @is_continuous_operator_algebra R X NX continuous_operator_algebra_witness J ZN.
Proof.
constructor; first exact hZ.
- exact: operator_algebra_unit_witnessE.
- exact: operator_algebra_product_witnessE.
Qed.
End Witness.
