(** Federer (1969), 4.1.24, p. 381: both original
    polyhedral classes lie in the normal and flat classes.
    The generators and exact compact index are those of
    4.1.22, p. 379. These adapters reuse their proved
    normality and the earlier normal-to-flat inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import ModuleQuotient Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces NormalCurrentsUP FlatCurrentsUP FlatCurrentFinite
  PolyhedralCurrentAlgebra PolyhedralNormal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section PolyhedralCurrentFlat.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Variable T:@current_space R h2 n U hU m.

(** Source for [integral_polyhedral_current_flat_supported]:
    the original integral polyhedral current is flat with
    its original K, by its supported normality. This
    supplies the actual image domain used in 4.1.24,
    p. 380, from 4.1.22, p. 379. *)
Theorem integral_polyhedral_current_flat_supported:
  @integral_polyhedral_current_class R h2 n m U hU K T->
  @is_flat_current_supported_in R h2 n m U hU K T.
Proof.
move=>hT;apply:supported_normal_current_is_flat.
exact:(@integral_polyhedral_current_normal_support R h2 n m U hU K T hT).
Qed.

(** Source for [real_polyhedral_current_flat_supported]:
    the original real polyhedral current has the same
    exact compact flat inclusion, in the diagram of
    4.1.24, p. 381, by 4.1.22's real span. *)
Theorem real_polyhedral_current_flat_supported:
  @polyhedral_current_subspace R h2 n m U hU K T->
  @is_flat_current_supported_in R h2 n m U hU K T.
Proof.
move=>hT;apply:supported_normal_current_is_flat.
exact:(@real_polyhedral_current_normal_support R h2 n m U hU K T hT).
Qed.
End PolyhedralCurrentFlat.
