(** Federer (1969), 3.1.11, pp. 218–219:
    exact public higher-differential graph laws and
    existence of representatives on the actual domain.
    The recursive graph witness remains behind its seal. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP PartialFunctionUP PartialFunctionExtensionUP
  PartialFunctionExtensionSealed ContinuousMultilinearUP NormHigherDifferentialUP
  NormHigherDifferentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section GraphLaws.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k).
Variable A : X->Prop.
Variable f : X->Y.

(** Source for [norm_higher_differential]: the partial map
    D^k f of Federer 3.1.11, pp. 218–219, exposed
    through the sealed exact graph, without default values. *)
Definition norm_higher_differential k : partial_function X (Z k) :=
  @NormHigherDifferential.value R X Y NX NY hNX hNY Z evaluation ZN hZ A f k.

(** Source for [norm_higher_differential_graph]: the exact
    recursive characterization of D^k f(a) in Federer
    3.1.11, pp. 218–219. *)
Lemma norm_higher_differential_graph k a z :
  partial_function_graph (norm_higher_differential k) a z <->
  has_norm_higher_differential NX evaluation ZN A f k a z.
Proof. exact: (@NormHigherDifferential.laws R X Y NX NY hNX hNY Z evaluation ZN hZ A f k a z). Qed.

(** Source for [norm_higher_differential_representative_exists]:
    an auxiliary representative of D^k f may be used
    on its exact domain in the recursion, Federer
    3.1.11, p. 219. Only existence is asserted;
    no value outside that domain is part of D^k f. *)
Lemma norm_higher_differential_representative_exists k :
  exists g : X->Z k, forall x w,
    has_norm_higher_differential NX evaluation ZN A f k x w -> g x=w.
Proof.
exists (@PartialFunctionExtension.value X (Z k) (norm_higher_differential k) 0).
move=> x w hw; apply: (@PartialFunctionExtension.laws X (Z k) _ 0 x w).
exact ((@norm_higher_differential_graph k x w).2 hw).
Qed.
End GraphLaws.
