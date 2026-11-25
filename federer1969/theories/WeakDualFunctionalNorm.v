(** Federer (1969), 4.1.5, p. 349: the
    continuous real dual in the earlier Radon–Daniell
    theorem is identified with the actual abstract
    continuous dual. Its unit-sphere supremum is
    the same least nonnegative evaluation bound,
    including the zero target space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP RealFunctionalNormUP VectorDaniellHypotheses
  VectorDaniellDualExtension DualNormEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section WeakDualFunctionalNorm.
Variable R:realType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.

(** Source for [weak_dual_functional_linear]: a member of
    the original weak Y* is a real linear functional,
    Federer 4.1.5, p. 349, using 2.5.12(2). *)
Lemma weak_dual_functional_linear (alpha:weak_dual_space hNY):
  linear (val alpha:Y->R^o).
Proof.
move=>c u v; exact:(@dual_space_linear R Y NY hNY (val alpha) (set_valP alpha) c u v).
Qed.

(** Source for [weak_dual_functional_hom]: the original
    evaluation as a Hom, supporting transport to the
    abstract Y* in Federer 4.1.5, p. 349. *)
Definition weak_dual_functional_hom (alpha:weak_dual_space hNY):Hom Y R^o:=
  @HomMap R Y R^o (val alpha) (introT (asboolP _) (weak_dual_functional_linear alpha)).

(** Source for [weak_dual_functional_norm_nonnegative]:
    nonnegativity of the original dual norm, supporting
    Federer 4.1.5, p. 349. Empty unit spheres have
    supremum zero and require no nonzero-target premise. *)
Lemma weak_dual_functional_norm_nonnegative (alpha:weak_dual_space hNY):
  0<=dual_norm NY (val alpha).
Proof.
case:(pselect ([set y:Y|NY y= 1]!=set0))=>hSphere.
- have[y hy]:=hSphere.
  have[C [hC hBound]]:=@dual_space_bounded R Y NY hNY (val alpha) (set_valP alpha).
  have hSup:has_sup [set val alpha y|y in [set y:Y|NY y= 1]].
    split; first by exists (val alpha y); exists y.
    exists C=>_ [z hz <-].
    have h:=le_trans (ler_norm (val alpha z)) (hBound z); by rewrite hz mulr1 in h.
  have hPlus:=sup_upper_bound hSup (imageP (val alpha) hy).
  have hNegative:NY (-y)= 1 by rewrite (real_seminorm_negate hNY.1).
  have hMinus:=sup_upper_bound hSup (imageP (val alpha) hNegative).
  rewrite -scaleN1r (@dual_space_scale R Y NY hNY (val alpha) (-1) y (set_valP alpha)) mulN1r in hMinus.
  change (is_true (val alpha y<=dual_norm NY (val alpha))) in hPlus.
  change (is_true (-val alpha y<=dual_norm NY (val alpha))) in hMinus.
  lra.
- have hEmpty:[set val alpha y|y in [set y:Y|NY y= 1]]=set0.
    apply/seteqP; split=>[a [y hy _]|a []].
    exfalso; apply:hSphere; by exists y.
  by rewrite /dual_norm hEmpty sup0.
Qed.

(** Source for [weak_dual_functional_norm_least]: the
    original dual norm is the least nonnegative
    evaluation bound, for the abstract dual identification
    in Federer 4.1.5, p. 349. *)
Lemma weak_dual_functional_norm_least (alpha:weak_dual_space hNY) C:
  0<=C ->(forall y,`|val alpha y|<=C*NY y) ->dual_norm NY (val alpha)<=C.
Proof.
move=>hC hBound; rewrite /dual_norm.
case:(pselect ([set val alpha y|y in [set y:Y|NY y= 1]]!=set0))=>hNonempty.
- apply:ge_sup hNonempty _=>a [y hy <-].
  have h:=le_trans (ler_norm (val alpha y)) (hBound y); by rewrite hy mulr1 in h.
- have hEmpty:[set val alpha y|y in [set y:Y|NY y= 1]]=set0.
    apply/seteqP; split=>[a ha|a []]; exfalso; apply:hNonempty; by exists a.
  by rewrite hEmpty sup0.
Qed.

(** Source for [weak_dual_functional_norm_laws]: the old
    weak dual and the actual abstract Y* have exactly
    the same original norm, Federer 4.1.5, p. 349. *)
Theorem weak_dual_functional_norm_laws (alpha:weak_dual_space hNY):
  is_real_functional_norm NY (hom_as_linear (weak_dual_functional_hom alpha)) (dual_norm NY (val alpha)).
Proof.
constructor.
- exact:weak_dual_functional_norm_nonnegative.
- move=>y; exact:(@dual_norm_evaluation_bound R Y NY hNY (val alpha) y (set_valP alpha)).
- move=>C hC hBound; exact:weak_dual_functional_norm_least hC hBound.
Qed.
End WeakDualFunctionalNorm.
