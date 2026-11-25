(** Supporting the scalar sections in Federer (1969), 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, Parts 3–4, pp. 244–247. Solving w=a*t+b
    identifies each section with an affine image of the scalar factor. Borel
    status is proved by the inverse affine map, using 2.2.14, p. 70. Source
    context and homothety comparison: ScalarAffineLebesgue.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground TopologicalBorel ContinuousBorelPreimages
  LebesgueScalarMeasure BorelRegularMeasureUP ScalarAffineLebesgue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_affine_section_image]: supporting scalar
    inverse-image calculation for 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, Part 3,
    pp. 244–245. A nonzero slope gives one
    and only one parameter t for each scalar image point. *)
Lemma scalar_affine_section_image (R : realType) (a b : R) (T : set R) :
  a!=0 -> [set w | T ((w-b)/a)]=(fun t=>a*t+b) @` T.
Proof.
move=> ha; apply/seteqP; split=> w.
- move=> hw; exists ((w-b)/a)=> //; by rewrite mulrC divfK // subrK.
- move=> [t ht <-]; by rewrite /= addrK [a*t]mulrC mulfK.
Qed.

(** Source for [scalar_affine_section_borel]: supporting Borel
    sections for 2.10.46, p. 204; Freilich
    (1950), Theorem 4.5, Part 4, pp. 245–247.
    The inverse affine map is continuous, so Borel factors
    yield Borel sections. *)
Lemma scalar_affine_section_borel (R : realType) (a b : R) (T : set (real_line_metric R)) :
  borel_set T -> @borel_set [the topologicalType of real_line_metric R] [set w | T ((w-b)/a)].
Proof.
move=> hT; apply: (@continuous_borel_preimage [the topologicalType of real_line_metric R]
  [the topologicalType of real_line_metric R] (fun w=>(w-b)/a) _ T hT).
move=> w; apply: (@continuousM R [the topologicalType of real_line_metric R]
  (fun z=>z-b) (fun _=>a^-1) w); last exact: cvg_cst.
apply: (@continuousB R R^o [the topologicalType of real_line_metric R]
  id (fun _=>b) w); [exact: cvg_id|exact: cvg_cst].
Qed.

(** Source for [scalar_affine_section_measure]: supporting equal
    section-length calculation for 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, Parts 3–4,
    pp. 244–247. The value is independent of
    the translation and remains valid for arbitrary scalar sets. *)
Lemma scalar_affine_section_measure (R : realType) (a b : R) (T : set R) :
  a!=0 -> lebesgue_scalar_measure [set w | T ((w-b)/a)]=
    (`|a|%:E*lebesgue_scalar_measure T)%E.
Proof. move=> ha; rewrite (@scalar_affine_section_image R a b T ha); exact: scalar_affine_lebesgue_image. Qed.
