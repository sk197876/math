(** Federer (1969), 3.1.11, pp. 220–221:
    linearity and constant values of the normed-vector
    Stieltjes limits in Taylor's formula. These laws
    follow directly from the specified tagged-sum limit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology normedtype lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP StieltjesSums
  StieltjesIntegral RealMetricBackground CurveVariationUP CurveArcLength NormedStieltjesUP NormedStieltjesSums.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [normed_stieltjes_integral_add]:
    linearity of the Taylor integral in Federer
    3.1.11, pp. 220–221, using the finite-sum
    linearity of 2.5.17, p. 111. Existence
    of both supplied integrals is part of the hypotheses. *)
Theorem normed_stieltjes_integral_add (R : realType) (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (f q : R->Y) (g : R->R) (a b : R) (u v : Y) :
  has_normed_stieltjes_integral NY f g a b u ->
  has_normed_stieltjes_integral NY q g a b v ->
  has_normed_stieltjes_integral NY (fun t=>f t+q t) g a b (u+v).
Proof.
move=> [hab hf] [_ hq]; split; first exact hab.
move=> e he; have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [r [hr hrf]] := hf _ he2.
have [s [hs hsq]] := hq _ he2.
exists (Num.min r s); split; first by rewrite lt_min hr hs.
move=> w hw hm.
have hmr : Num.min r s<=r by rewrite ge_min lexx.
have hms : Num.min r s<=s by rewrite ge_min lexx orbT.
have h1 := hrf w hw (tagged_mesh_lt_le hmr hm).
have h2 := hsq w hw (tagged_mesh_lt_le hms hm).
rewrite normed_stieltjes_sum_add opprD addrACA.
have ht := real_seminorm_triangle hNY.1
  (normed_stieltjes_sum f g w-u) (normed_stieltjes_sum q g w-v).
have hb := le_lt_trans ht (ltrD h1 h2).
have hid : e/2+e/2=e by lra.
by rewrite hid in hb.
Qed.

(** Source for [normed_stieltjes_integral_linear_image]:
    a bounded linear map commutes with an existing
    vector-valued Stieltjes limit, supporting the contractions
    in the Taylor formula of Federer 3.1.11,
    pp. 220–221. *)
Theorem normed_stieltjes_integral_linear_image (R : realType)
    (Y Z : lmodType R) (NY : Y->R) (NZ : Z->R)
    (f : R->Y) (g : R->R) (a b : R) (v : Y) (L : Hom Y Z) :
  norm_bounded_linear NY NZ L ->
  has_normed_stieltjes_integral NY f g a b v ->
  has_normed_stieltjes_integral NZ (fun t=>L (f t)) g a b (L v).
Proof.
move=> [C [hC hL]] [hab hv]; split; first exact hab.
move=> e he.
have hCp : 0<C+1 by lra.
have heC : 0<e/(C+1) by rewrite divr_gt0.
have [d [hd hb]] := hv _ heC.
exists d; split=> // w hw hm.
rewrite normed_stieltjes_sum_linear_image -linearB.
apply: le_lt_trans (hL _) _.
have hsmall := hb w hw hm.
have hle := ler_wpM2l hC (ltW hsmall).
have heq : (e/(C+1))*(C+1)=e by rewrite divfK // gt_eqF.
have hstrict : C*(e/(C+1))<e by nra.
exact: le_lt_trans hle hstrict.
Qed.

(** Source for [normed_stieltjes_integral_constant]:
    a constant integrand integrates to its value times
    the integrator's endpoint increment, supporting the
    Taylor normalization in Federer 3.1.11, pp. 220–221. *)
Theorem normed_stieltjes_integral_constant (R : realType) (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY) (g : R->R)
    (a b : R) (c : Y) :
  a<=b -> has_normed_stieltjes_integral NY (fun _=>c) g a b ((g b-g a)*:c).
Proof.
move=> hab; split; first exact hab.
move=> e he; exists 1; split; first exact: ltr01.
move=> w hw _; by rewrite (@normed_stieltjes_sum_constant R Y g c a b w hw)
  subrr (real_seminorm_zero hNY.1).
Qed.

(** Source for [normed_stieltjes_scalar_agreement]:
    the vector-valued limit reduces to the already
    formalised scalar integral of Federer 2.5.17,
    pp. 110–111, in the scalar Taylor case of
    3.1.11, p. 220. *)
Theorem normed_stieltjes_scalar_agreement (R : realType)
    (f g : R->R) (a b : R) :
  curve_locally_finite_variation (g : R->real_line_metric R) ->
  continuous f -> a<=b ->
  has_normed_stieltjes_integral (fun t : R^o=>`|t|) f g a b
    (stieltjes_integral g f a b).
Proof.
move=> hg hf hab; split; first exact hab.
move=> e he; have [d [hd hb]] := stieltjes_integral_limit hg hf hab he.
exists d; split=> // w hw hm.
rewrite normed_stieltjes_sum_scalar; exact: hb w hw hm.
Qed.


(** Source for [normed_stieltjes_integral_ext]:
    equality of representatives preserves the tagged
    sums and their limit, supporting Federer
    3.1.11, pp. 220–221. *)
Lemma normed_stieltjes_integral_ext (R : realType) (Y : lmodType R)
    (NY : Y->R) (f q : R->Y) (g r : R->R)
    (a b : R) (v : Y) :
  f =1 q -> g =1 r ->
  has_normed_stieltjes_integral NY f g a b v ->
  has_normed_stieltjes_integral NY q r a b v.
Proof. move=> hf hg; by rewrite -(funext hf) -(funext hg). Qed.

(** Source for [normed_stieltjes_integral_scale]:
    scalar linearity of the actual Taylor integral,
    supporting the factorial normalization in Federer
    3.1.11, pp. 220–221. *)
Lemma normed_stieltjes_integral_scale (R : realType) (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (f : R->Y) (g : R->R) (a b c : R) (v : Y) :
  has_normed_stieltjes_integral NY f g a b v ->
  has_normed_stieltjes_integral NY (fun t=>c*:f t) g a b (c*:v).
Proof.
move=> [hab hf]; split; first exact hab.
move=> e he.
have hc := normr_ge0 c.
have hden : 0<`|c|+1 by lra.
have hp : 0<e/(`|c|+1) by rewrite divr_gt0.
have [d [hd hdf]] := hf _ hp.
exists d; split=> // w hw hm.
rewrite normed_stieltjes_sum_scale -scalerBr (real_seminorm_scale hNY.1).
have hb := hdf w hw hm.
have hn := real_seminorm_nonnegative hNY.1 (normed_stieltjes_sum f g w-v).
have hid : (e/(`|c|+1))*(`|c|+1)=e by rewrite divfK // gt_eqF.
nra.
Qed.

(** Source for [normed_stieltjes_integral_subtract]:
    subtraction of the constant highest-derivative term
    in the Taylor remainder, Federer 3.1.11,
    pp. 220–221. Both integral values are
    proved limits before this law is applied. *)
Lemma normed_stieltjes_integral_subtract (R : realType) (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (f q : R->Y) (g : R->R) (a b : R) (u v : Y) :
  has_normed_stieltjes_integral NY f g a b u ->
  has_normed_stieltjes_integral NY q g a b v ->
  has_normed_stieltjes_integral NY (fun t=>f t-q t) g a b (u-v).
Proof.
move=> hf hq.
have hn := normed_stieltjes_integral_scale hNY (-1) hq.
have hs := normed_stieltjes_integral_add hNY hf hn.
rewrite scaleN1r in hs.
apply: normed_stieltjes_integral_ext _ _ hs=>t //.
by rewrite scaleN1r.
Qed.
