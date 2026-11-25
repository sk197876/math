(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3;
    blueprint dgpr_blueprint.tex, lem:regularity and the statement of
    lem:DGPR31: the field DB of space differentials of B. For t < T the
    section [x |-> B(t,x)] has the differential D B(t,x) o i at x, where
    i(x) = (0,x), by the chain rule of Federer 3.1.1, p. 210, for the
    affine map [x |-> (t,x)]; B is of class 1 on Omega_T by
    lem:regularity. Hence the hypothesis [hDB] of DgprLemma31Final.v and
    DgprLemma32Final.v is satisfied by some field DB. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormMetric HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm InnerProductUP ScalarInnerProduct ProductInner
  LinearBasis HomInner HomInnerCoordinates
  NormDifferentialUP NormDifferentialLinear NormDifferentialArithmetic NormDifferentialChain
  NormOpenDomainLaws NormClassOneUP NormRegularity SmoothFunctionSpaceUP SmoothTestSpaces.
From DPGPR Require Import DgprDifferentialCalculus DgprGrowthClasses DgprStanding DgprHeatObjects
  DgprIdentitiesSmooth DgprHeatIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section SliceDifferential.
Variable R : realType.
Variable n : nat.
Variable T : R.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BT := (product_inner_productP (scalar_inner_productP R)
  (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Local Notation inj := (dgpr_space_injection R n).

(** Source for [dgpr_slice_differential]: if G has the differential L at
    (t,x) relative to Omega_T, then the section [z |-> G(t,z)] has the
    differential L o i at x, where i(z) = (0,z); chain rule of Federer
    3.1.1, p. 210, for the affine map [z |-> i(z) + (t,0)]. *)
Lemma dgpr_slice_differential (W : lmodType R) (NW : W -> R) (hNW : is_real_norm NW)
    (G : TX -> W) (t : R) (x : X) (L : Hom TX W) : t < T ->
  has_norm_differential NT NW (dgpr_before T) G (t, x) L ->
  has_norm_differential N NW setT (fun z => G (t, z)) x (hom_comp L inj).
Proof.
move=> ht hG.
pose bt : TX := ((t : R^o), (0 : X)).
have hLb : norm_bounded_linear N NT inj.
  by exists 1; split => // z; exact: dgpr_space_injection_bound.
have hc : has_norm_differential N NT (fun _ => True) (fun z : X => inj z + bt) x (inj + 0).
  exact: (norm_differential_add hNT (norm_differential_linear hN hNT (norm_full_domain_interior N x) hLb)
    (norm_differential_constant hN hNT bt (norm_full_domain_interior N x))).
rewrite -(dgpr_space_affine t x) in hG.
have hch := norm_differential_chain hN hNT hNW hc hG.
have ef : (fun z : X => G (inj z + bt)) = (fun z => G (t, z)).
  by apply: funext => z; rewrite dgpr_space_affine.
have eA : (fun z : X => True /\ dgpr_before T (inj z + bt)) = setT.
  apply: funext => z; apply: propext; split => // _; split => //.
  by rewrite /bt dgpr_space_affine.
by rewrite ef eA addr0 in hch.
Qed.
End SliceDifferential.

Section Lemma31Field.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable d : nat.
Variable eY : 'I_d -> Y.
Hypothesis heY : is_basis eY.
Hypothesis hm : (0 < m <= n)%N.
Local Notation NY := (inner_norm hCY).
Local Notation hNY := (inner_norm_real_norm hCY).
Local Notation BH := (hom_inner_productP BX hCY heX).
Local Notation NH := (hom_norm BX hCY heX).
Local Notation hNH := (inner_norm_real_norm BH).
Variable K : set (real_norm_metric_space hNH).
Variables lam Lam : R.
Variable mu : set X -> \bar R.
Variable r0 : R.
Variable Xf : X -> Hom X Y.
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.
Variable Ups : Hom (smooth_test_space hE) R^o.
Variable ups : set (real_norm_metric_space hN) -> \bar R.
Variable dups : X -> Hom Y R^o.
Variable delta : R.
Variable T : R.
Variable mu0 : set X -> \bar R.
Variable gamma : R.
Hypothesis hS : dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T mu0 gamma.
Local Notation B := (dgpr_heat_B hS).

(** Source for [dgpr_lemma31_DB_exists]: lem:regularity (B is of class
    infinity on Omega_T) and [dgpr_slice_differential]: there is a field
    DB whose values at (t,x), for t < T, are those of D B_t(x). *)
Theorem dgpr_lemma31_DB_exists : exists DB : TX -> X -> Hom X Y,
  forall t x, t < T -> dgpr_differential_values NH (fun z => B (t, z)) x (DB (t, x)).
Proof.
have [hB _ _ _] := dgpr_regularity_smooth hS.
have /norm_class_firstP [D hD] := hB 1%N.
exists (fun p => (hom_comp (D p) (dgpr_space_injection R n) : X -> Hom X Y)) => t x ht.
exists (hom_comp (D (t, x)) (dgpr_space_injection R n)); split => //.
exact: (dgpr_slice_differential hNH ht (norm_class_one_differential hD (ht : dgpr_before T (t, x)))).
Qed.
End Lemma31Field.
