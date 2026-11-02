(** Public normed function space E=K(Y), Federer (1969), 2.5.20, p. 114.
    Evaluation and uniform-norm laws follow only from the sealed abstract
    interface. Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_algebra reals topology.
From Federer Require Import CompactFunctionSpaceUP CompactFunctionSpaceLaws
  CompactFunctionSpaceSealed RealNormUP NormMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [compact_function_space]: E=K(Y) in Federer 2.5.20, p. 114. *)
Definition compact_function_space (R : realType) (Y : topologicalType) : lmodType R :=
  CompactFunctionSpace.space R Y.

(** Source for [compact_function_evaluate]: evaluation of the
    vectors of K(Y), Federer 2.5.20, p. 114. *)
Definition compact_function_evaluate (R : realType) (Y : topologicalType)
    (f : compact_function_space R Y) := @CompactFunctionSpace.value R Y f.

(** Source for [compact_function_space_specification]: the
    abstract function-space laws of Federer 2.5.20, p. 114,
    supplied by the sealed existence theorem. *)
Theorem compact_function_space_specification (R : realType) (Y : topologicalType) :
  is_compact_function_space (@compact_function_evaluate R Y).
Proof. exact: (@CompactFunctionSpace.laws R Y). Qed.

(** Source for [compact_function_space_norm]: the displayed
    supremum norm nu on K(Y), Federer 2.5.20, p. 114. *)
Definition compact_function_space_norm (R : realType) (Y : topologicalType) :=
  @compact_function_norm R Y (compact_function_space R Y) (@compact_function_evaluate R Y).

(** Source for [compact_function_space_norm_laws]: norm laws
    supporting the application of 2.5.12 in Federer 2.5.20,
    p. 114. An empty Y produces the zero normed space. *)
Definition compact_function_space_norm_laws (R : realType) (Y : topologicalType) :
  is_real_norm (@compact_function_space_norm R Y) :=
  compact_function_norm_laws (@compact_function_space_specification R Y).
