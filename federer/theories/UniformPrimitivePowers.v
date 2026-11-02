(** Supporting square and cube primitive rules for the elementary rational
    integrals in Federer (1969), 2.6.3(2), pp. 117–118 These are
    consequences of the proved finite-increment product rule. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology normedtype ring.
From Federer Require Import UniformPrimitiveUP UniformPrimitiveAlgebra UniformPrimitiveProduct
  StieltjesDaniellIntegral ReciprocalPrimitive.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [continuous_real_square]: supporting continuity
    of the reciprocal polynomial expressions used in Federer
    2.6.3(2), pp. 117–118. *)
Lemma continuous_real_square (R : realType) (F : R -> R) :
  continuous F -> continuous (fun x => (F x)^+2).
Proof.
move=> hF.
have he : (fun x => (F x)^+2) = (fun x => F x*F x) by apply: funext=> x; rewrite expr2.
rewrite he=> x; exact: cvgM (hF x) (hF x).
Qed.

(** Source for [continuous_real_cube]: supporting continuity
    of the primitive expressions used in Federer 2.6.3(2),
    pp. 117–118. *)
Lemma continuous_real_cube (R : realType) (F : R -> R) :
  continuous F -> continuous (fun x => (F x)^+3).
Proof.
move=> hF.
have he : (fun x => (F x)^+3) = (fun x => F x*(F x)^+2) by apply: funext=> x; rewrite exprS.
have h2 : continuous (fun x => (F x)^+2) := continuous_real_square hF.
rewrite he=> x; exact: cvgM (hF x) (h2 x).
Qed.

(** Source for [uniform_primitive_square]: supporting square primitive rule
    for Federer 2.6.3(2), pp. 117–118 *)
Lemma uniform_primitive_square (R : realType) (f F : R -> R) (a b : R) :
  continuous f -> continuous F -> is_uniform_primitive_on f F a b ->
  is_uniform_primitive_on (fun x => 2*F x*f x) (fun x => (F x)^+2) a b.
Proof.
move=> hf hF hp.
have h := uniform_primitive_product hf hF hf hF hp hp.
apply: (@uniform_primitive_ext R _ _ _ _ a b _ h)=> x _; split; ring.
Qed.

(** Source for [uniform_primitive_cube]: supporting cube primitive rule for
    Federer 2.6.3(2), pp. 117–118 *)
Lemma uniform_primitive_cube (R : realType) (f F : R -> R) (a b : R) :
  continuous f -> continuous F -> is_uniform_primitive_on f F a b ->
  is_uniform_primitive_on (fun x => 3*(F x)^+2*f x) (fun x => (F x)^+3) a b.
Proof.
move=> hf hF hp.
have hd : continuous (fun x => 2*F x*f x).
  have hc : continuous (fun x => 2*F x) := continuous_scale (c:=2) hF.
  move=> x; exact: cvgM (hc x) (hf x).
have h := uniform_primitive_product hd (continuous_real_square hF) hf hF
  (uniform_primitive_square hf hF hp) hp.
apply: (@uniform_primitive_ext R _ _ _ _ a b _ h)=> x _; split; ring.
Qed.

(** Source for [reciprocal_square_uniform_primitive]: the
    inverse-square primitive rule supporting the elementary
    formulas of Federer 2.6.3(2), pp. 117–118. *)
Lemma reciprocal_square_uniform_primitive (R : realType) (U : R -> R) (a b : R) :
  continuous U -> is_uniform_primitive_on (fun x => -(U x)^+2) U a b ->
  is_uniform_primitive_on (fun x => -2*(U x)^+3) (fun x => (U x)^+2) a b.
Proof.
move=> hU hp.
have hf : continuous (fun x => -(U x)^+2).
  have h2 : continuous (fun x => (U x)^+2) := continuous_real_square hU.
  have he : (fun x => -(U x)^+2) = (fun x => (-1)*(U x)^+2).
    by apply: funext=> x; rewrite mulN1r.
  rewrite he; exact: continuous_scale h2.
have h := uniform_primitive_square hf hU hp.
apply: (@uniform_primitive_ext R _ _ _ _ a b _ h)=> x _; split; ring.
Qed.

(** Source for [reciprocal_cube_uniform_primitive]: the
    inverse-cube primitive rule supporting the elementary
    formulas of Federer 2.6.3(2), pp. 117–118. *)
Lemma reciprocal_cube_uniform_primitive (R : realType) (U : R -> R) (a b : R) :
  continuous U -> is_uniform_primitive_on (fun x => -(U x)^+2) U a b ->
  is_uniform_primitive_on (fun x => -3*(U x)^+4) (fun x => (U x)^+3) a b.
Proof.
move=> hU hp.
have hf : continuous (fun x => -(U x)^+2).
  have h2 : continuous (fun x => (U x)^+2) := continuous_real_square hU.
  have he : (fun x => -(U x)^+2) = (fun x => (-1)*(U x)^+2).
    by apply: funext=> x; rewrite mulN1r.
  rewrite he; exact: continuous_scale h2.
have h := uniform_primitive_cube hf hU hp.
apply: (@uniform_primitive_ext R _ _ _ _ a b _ h)=> x _; split; ring.
Qed.

(** Source for [continuous_real_fourth]: supporting continuity
    of the fourth reciprocal power in the rational kernel
    of Federer 2.6.3(2), p. 117. *)
Lemma continuous_real_fourth (R : realType) (F : R -> R) :
  continuous F -> continuous (fun x => (F x)^+4).
Proof.
move=> hF.
have he : (fun x => (F x)^+4) = (fun x => F x*(F x)^+3) by apply: funext=> x; rewrite exprS.
have h3 : continuous (fun x => (F x)^+3) := continuous_real_cube hF.
rewrite he=> x; exact: cvgM (hF x) (h3 x).
Qed.
