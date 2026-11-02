(** Federer (1969), 3.2.3, pp. 243–244: the
    injective differential and singular differential cases are
    separated by positivity or vanishing of the top-source
    Jacobian. All domains are actual differential domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormDifferentialUP EuclideanLinearJacobian JacobianUP Jacobian PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_linear_jacobian_zero_iff_singular]:
    the displayed critical-set equality in Federer 3.2.3,
    p. 243. Noninjectivity, equivalently a nonzero kernel,
    is exactly vanishing of the top-source Jacobian. *)
Lemma euclidean_linear_jacobian_zero_iff_singular (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)):
  euclidean_linear_jacobian m L=0 <-> ~injective L.
Proof.
split.
- move=>h0 hi; have hh:0<euclidean_linear_jacobian m L:=(euclidean_linear_jacobian_top_positive L).2 hi.
  by rewrite h0 ltxx in hh.
- move=>hi.
  have hPos:=euclidean_linear_jacobian_nonnegative m L.
  case:(ltP 0 (euclidean_linear_jacobian m L))=>[hgt|hle].
  + exfalso; exact (hi ((euclidean_linear_jacobian_top_positive L).1 hgt)).
  + by apply/eqP; rewrite eq_le hle hPos.
Qed.

(** Source for [singular_differential_locus]: the second
    case in Federer 3.2.3, pp. 243–244: an
    actual differential exists and has nonzero kernel. *)
Definition singular_differential_locus (R:realType) m n (f:R_n R m->R_n R n):set (R_n R m):=
  [set a|exists D:Hom (R_n R m) (R_n R n),has_norm_differential
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
    setT f a D /\ ~injective D].

(** Source for [singular_differential_locus_jacobian]: the
    displayed equality with {x:J_m f(x)=0} in
    Federer 3.2.3, p. 243. Undefined Jacobians
    are excluded from the zero-value set. *)
Lemma singular_differential_locus_jacobian (R:realType) m n
    (f:R_n R m->R_n R n) a:
  singular_differential_locus f a <-> partial_function_graph (euclidean_jacobian m setT f) a 0.
Proof.
split.
- move=>[D [hD hSing]]; apply:(euclidean_jacobian_graph m setT f a 0).2.
  exists D; split; first exact hD.
  exact ((euclidean_linear_jacobian_zero_iff_singular D).2 hSing).
- move=>/(euclidean_jacobian_graph m setT f a 0) [D [hD hZero]].
  exists D; split; first exact hD.
  exact ((euclidean_linear_jacobian_zero_iff_singular D).1 hZero).
Qed.
