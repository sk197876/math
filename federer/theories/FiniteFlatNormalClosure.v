(** Federer (1969), 4.1.12, p. 368: the
    original normal-current closure inside the complete
    finite-flat space. All carriers remain opaque;
    the closure uses the original inherited norm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  SmoothCompactSet CurrentFiniteFlatSpace CurrentFiniteFlatCompleteness
  NormalCurrentSpaces LinearSubspaceRepresentationUP NormClosureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteFlatNormalClosure.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation B := (@finite_flat_current_space R h2 n m U hU K).
Local Notation inc := (@finite_flat_current_inclusion R h2 n m U hU K).
Local Notation N := (@finite_flat_current_norm R h2 n m U hU K).
Local Notation hN := (@finite_flat_current_norm_is_norm R h2 n m U hU K).
Local Notation originalNormal := (@supported_normal_current_subspace R h2 n U hU m K).

(** Source for [finite_flat_normal_subspace]: the
    original N_(m,K)(U), regarded inside the finite-
    F_K current space, supporting Federer 4.1.12,
    p. 368. Use only the original linear inclusion
    and the preceding normal-subspace laws. *)
Definition finite_flat_normal_subspace:subspace B.
Proof.
refine (@Subspace R B (fun z=>originalNormal (inc z)) _ _ _).
- rewrite linear0;exact:subspace_zero.
- move=>x y hx hy;rewrite linearD;exact:subspace_add hx hy.
- move=>c x hx;rewrite linearZ;exact:subspace_scale hx.
Defined.

(** Source for [finite_flat_normal_closure_subspace]:
    the original F_K closure is a vector subspace,
    Federer 4.1.12, p. 368. Reuse the preceding
    norm-topology closure laws, without imposing a
    construction on any current or test space. *)
Definition finite_flat_normal_closure_subspace:subspace B.
Proof.
refine (@Subspace R B
  (fun z=>@closure (real_norm_metric_space hN) finite_flat_normal_subspace z) _ _ _).
- apply:subset_closure;exact:subspace_zero.
- move=>x y hx hy.
  apply:(@norm_closure_add_stable R B N hN finite_flat_normal_subspace _ x y hx hy).
  move=>a b ha hb;exact:subspace_add ha hb.
- move=>c x hx.
  apply:(@norm_closure_rational_scale_stable R B N hN finite_flat_normal_subspace _ c x hx).
  move=>q a ha;exact:subspace_scale ha.
Defined.

(** Source for [finite_flat_normal_closure_closed]: the
    original flat closure is closed in the complete
    finite-flat normed space, supporting its completeness
    in Federer 4.1.12, p. 368. *)
Lemma finite_flat_normal_closure_closed:
  closed (fun z:real_norm_metric_space hN=>finite_flat_normal_closure_subspace z).
Proof. exact:closed_closure. Qed.
End FiniteFlatNormalClosure.
